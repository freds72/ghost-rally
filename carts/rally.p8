pico-8 cartridge // http://www.pico-8.com
version 18
__lua__
-- ghost rally
-- by @freds72

-- globals
local time_t,time_dt=0,1/30
local actors,ground_actors,parts,v_light,cam,plyr,active_ground_actors={},{},{},{0,1,0}
local track,ghost

function nop() return true end

local physic_actors={}
-- physic thresholds
local k_small,k_small_v=0.001,0.01
-- baumgarte
local k_bias=0.2
local k_slop=0.05

-- world units
local ground_shift,hscale=1,4
local ground_scale=2^ground_shift
local ground_left,ground_right,ground_far,ground_near=-7,7,7,-7
local v_grav={0,-1,0}
local world={}
-- transitions mgt
local draw_state,update_state=nop,nop

-- track events
local on_new_lap=nop

-- zbuffer (kind of)
local drawables,zbuf
function zbuf_clear()
	drawables={}
end
function zbuf_sort()
 zbuf={}
	local ci,cj=flr(shr(cam.lookat[1],ground_shift)),flr(shr(cam.lookat[3],ground_shift))
	for _,d in pairs(drawables) do
		-- find cell location
		local di,dj=flr(shr(d.pos[1],ground_shift)),flr(shr(d.pos[3],ground_shift))
		-- todo: incorrect
		-- within viz grid?
		if abs(di-ci)<6 and abs(dj-cj)<10 then
			-- safe index
			dj=band(dj,0x7f)
			zbuf[dj]=zbuf[dj] or {}
			add(zbuf[dj],{obj=d,key=d.pos[3]})
		end
	end
	-- sort each bucket
	for _,b in pairs(zbuf) do
		sort(b)
	end
end

function zbuf_filter(array)
	for _,a in pairs(array) do
		if not a:update() then
			del(array,a)
		else
			add(drawables,a)
		end
	end
end

function clone(src,dst)
	-- safety checks
	if(src==dst) assert()
	if(type(src)!="table") assert()
	dst=dst or {}
	for k,v in pairs(src) do
		if(not dst[k]) dst[k]=v
	end
	-- randomize selected values
	if src.rnd then
		for k,v in pairs(src.rnd) do
			-- don't overwrite values
			if not dst[k] then
				dst[k]=v[3] and rndarray(v) or rndlerp(v[1],v[2])
			end
		end
	end
	return dst
end

function lerp(a,b,t)
	return a*(1-t)+b*t
end
function lerparray(a,t)
	return a[mid(flr((#a-1)*t+0.5),1,#a)]
end
function rndlerp(a,b)
	return lerp(b,a,1-rnd())
end
function smoothstep(t)
	t=mid(t,0,1)
	return t*t*(3-2*t)
end
function rndrng(ab)
	return flr(rndlerp(ab[1],ab[2]))
end
function rndarray(a)
	return a[flr(rnd(#a))+1]
end

-- https://github.com/morgan3d/misc/tree/master/p8sort
function sort(data)
 for num_sorted=1,#data-1 do 
  local new_val=data[num_sorted+1]
  local new_val_key=new_val.key
  local i=num_sorted+1

  while i>1 and new_val_key>data[i-1].key do
   data[i]=data[i-1]   
   i-=1
  end
  data[i]=new_val
 end
end

-- vector math
function sqr_dist(a,b)
	local dx,dy,dz=b[1]-a[1],b[2]-a[2],b[3]-a[3]

	dx=dx*dx+dy*dy+dz*dz
	return dx<0 and 32000 or dx
end
-- safe dist function
function v_xz_dist(v)
	local x,z=v[1],v[3]
	local scale=max(abs(x),abs(z))
	x/=scale
	z/=scale
	return scale*(x*x+z*z)^.5
end

function make_v_cross(a,b)
	local ax,ay,az=a[1],a[2],a[3]
	local bx,by,bz=b[1],b[2],b[3]
	return {ay*bz-az*by,az*bx-ax*bz,ax*by-ay*bx}
end
-- world axis
local v_fwd,v_right,v_up,v_zero={0,0,1},{1,0,0},{0,1,0},function() return {0,0,0} end

function make_v(a,b)
	return {
		b[1]-a[1],
		b[2]-a[2],
		b[3]-a[3]}
end
function v_clone(v)
	return {v[1],v[2],v[3]}
end
function v_dot(a,b)
	return a[1]*b[1]+a[2]*b[2]+a[3]*b[3]
end
function v_sqr(a)
	return {a[1]*a[1],a[2]*a[2],a[3]*a[3]}
end

function v_normz(v)
	local d=v_dot(v,v)
	if d>0.001 then
		d=sqrt(d)
		v[1]/=d
		v[2]/=d
		v[3]/=d
	end
	return d
end
function v_scale(v,scale)
	v[1]*=scale
	v[2]*=scale
	v[3]*=scale
end
function v_add(v,dv,scale)
	scale=scale or 1
	v[1]+=scale*dv[1]
	v[2]+=scale*dv[2]
	v[3]+=scale*dv[3]
end
function v_min(a,b)
	return {min(a[1],b[1]),min(a[2],b[2]),min(a[3],b[3])}
end
function v_max(a,b)
	return {max(a[1],b[1]),max(a[2],b[2]),max(a[3],b[3])}
end

function serialize(v,state)
	for i=1,#v do
		add(state,v[i])
	end
end
function deserialize(state,k,v)
	for i=1,#v do
		v[i]=state[k]
		k+=1
	end
	return k
end

-- 3x3 matrix operations
function make_m(x,y,z)
	return {
		x or 1,0,0,
		0,y or 1,0,
		0,0,z or 1}
end
function m_x_v(m,v)
	local x,y,z=v[1],v[2],v[3]
	return {m[1]*x+m[4]*y+m[7]*z,m[2]*x+m[5]*y+m[8]*z,m[3]*x+m[6]*y+m[9]*z}
end
-- inplace matrix multiply invert
function m_inv_x_v(m,v)
	local x,y,z=v[1],v[2],v[3]
	v[1],v[2],v[3]=m[1]*x+m[2]*y+m[3]*z,m[4]*x+m[5]*y+m[6]*z,m[7]*x+m[8]*y+m[9]*z
end

-- generic matrix inverse
function m_inv(me)
	local te={
	me[9]*me[5]-me[6]*me[8],me[9]*me[2]+me[3]*me[8],me[6]*me[2]-me[3]*me[5],
	-me[9]*me[4]+me[6]*me[7],me[9]*me[1]-me[3]*me[7],-me[6]*me[1]+me[3]*me[4],
	me[9]*me[4]-me[5]*me[8],-me[8]*me[1]+me[2]*me[7],me[5]*me[1]-me[2]*me[4]}

	local det = me[1]*te[1]+me[2]*te[4]+me[3]*te[7]
	-- not inversible?
	assert(det>0)
	m_scale(te,1/det)
	return te
end

function m_scale(m,scale)
	for i=1,#m do
		m[i]*=scale
	end
end
-- matrix transpose
function m_transpose(m)
	return {
		m[1],m[4],m[7],
		m[2],m[5],m[8],
		m[3],m[6],m[9]}
end
-- matrix 
function m_x_m(a,b)
	local a11,a12,a13=a[1],a[4],a[7]
	local a21,a22,a23=a[2],a[5],a[8]
	local a31,a32,a33=a[3],a[6],a[9]
	local b11,b12,b13=b[1],b[4],b[7]
	local b21,b22,b23=b[2],b[5],b[8]
	local b31,b32,b33=b[3],b[6],b[9]
	
 return {
		a11*b11+a12*b21+a13*b31,
		a21*b11+a22*b21+a23*b31,
		a31*b11+a32*b21+a33*b31,
		a11*b12+a12*b22+a13*b32,
		a21*b12+a22*b22+a23*b32,
		a31*b12+a32*b22+a33*b32,
		a11*b13+a12*b23+a13*b33,
		a21*b13+a22*b23+a23*b33,
		a31*b13+a32*b23+a33*b33
    }
end

-- returns right vector from matrix
function m_right(m)
	return {m[1],m[2],m[3]}
end
-- returns up vector from matrix
function m_up(m)
	return {m[4],m[5],m[6]}
end
-- returns foward vector from matrix
function m_fwd(m)
	return {m[7],m[8],m[9]}
end

-- quaternion
function make_q(v,angle)
	angle/=2
	-- fix pico sin
	local s=-sin(angle)
	return {v[1]*s,
	        v[2]*s,
	        v[3]*s,
	        cos(angle)}
end
function q_clone(q)
	return {q[1],q[2],q[3],q[4]}
end
function q_normz(q)
	local d=v_dot(q,q)+q[4]*q[4]
	if d>0 then
		d=sqrt(d)
		q[1]/=d
		q[2]/=d
		q[3]/=d
		q[4]/=d
	end
end
function q_dydt(q,v,dt)
	local dq={v[1]*dt,v[2]*dt,v[3]*dt,0}
	q_x_q(dq,q)

	q[1]+=0.5*dq[1]
	q[2]+=0.5*dq[2]
	q[3]+=0.5*dq[3]
	q[4]+=0.5*dq[4]
	q_normz(q)
end

function q_x_q(a,b)
	local qax,qay,qaz,qaw=a[1],a[2],a[3],a[4]
	local qbx,qby,qbz,qbw=b[1],b[2],b[3],b[4]
        
	a[1]=qax*qbw+qaw*qbx+qay*qbz-qaz*qby
	a[2]=qay*qbw+qaw*qby+qaz*qbx-qax*qbz
	a[3]=qaz*qbw+qaw*qbz+qax*qby-qay*qbx
	a[4]=qaw*qbw-qax*qbx-qay*qby-qaz*qbz
end
function m_from_q(q)
	local x,y,z,w=q[1],q[2],q[3],q[4]
	local x2,y2,z2=x+x,y+y,z+z
	local xx,xy,xz=x*x2,x*y2,x*z2
	local yy,yz,zz=y*y2,y*z2,z*z2
	local wx,wy,wz=w*x2,w*y2,w*z2

	return {
		1-(yy+zz),xy+wz,xz-wy,
		xy-wz,1-(xx+zz),yz+wx,
		xz+wy,yz-wx,1-(xx+yy)}
end

-- models & rendering
local all_models={}
local dither_pat2={0xffff,0xa5a5,0x0000}

function draw_model(model,m,pos,outline)
	-- cam pos in object space
	local cam_pos=make_v(pos,cam.pos)
	m_inv_x_v(m,cam_pos)
	
	-- faces
	local faces,p={},{}
	for _,f in pairs(model.f) do
		-- viz calculation
		if v_dot(f.n,cam_pos)>=f.cp then
			-- project vertices
			local z,verts=0,{}
			for ki,vi in pairs(f.vi) do
				local a=p[vi]
				if not a then
					local v=m_x_v(m,model.v[vi])
					v_add(v,pos)
					local x,y,z,w=cam:project(v)
					-- avoid rehash for u/v
					a={x,y,z,w}
					p[vi]=a
				end
				z+=a[3]
				local w=a[4]
				verts[ki]={a[1],a[2],w,f.uv[ki].u*w,f.uv[ki].v*w}
			end
			-- register faces
			add(faces,{key=#f.vi/z,face=f,v=verts})
		end
	end

	local pf=polyfill
	if outline then
		fillp(0xf0f0.f)
	else
		-- sort faces
		sort(faces)
		pf=polytex
	end
	
	-- draw faces using projected points
	for _,f in pairs(faces) do
		pf(f.v,1)
	end
	fillp()
end
function draw_model_shadow(model,m,pos)
 	fillp(0xa5a5.f)

	 -- v_light dir in object space
	local l=v_clone(v_light)
	m_inv_x_v(m,l)
	
	-- faces
	local p={}
	for _,f in pairs(model.f) do
		-- viz calculation
		if v_dot(f.n,l)<0 then
			-- project vertices
			local verts={}
			for ki,vi in pairs(f.vi) do
				local a=p[vi]
				if not a then
					local v=m_x_v(m,model.v[vi])
					v_add(v,pos)
					v[2]=get_altitude_and_n(v)
					local x,y,z,w=cam:project(v)
					a={x,y}
					p[vi]=a
				end
				verts[ki]=a
			end
			-- draw faces using projected points
			-- (no need to sort)
			polyfill(verts,1)
		end
	end
	fillp()
end

-- slip angle, slip ratio curves
local sa_curve,sr_curve
function apply_curve(curve,t)
	t=flr(31*mid(t,0,1))+1
	-- smooth curve
	-- sfx range is 0-60
	return lerp(curve[t],curve[min(32,t+1)],t%1)/60
end

function ssprt(self,s,x,y,z,w)	
	local x,y,z,w=cam:project(self.pos)
	-- behind cam?
	if(z>0) return
	palt(0,false)
	palt(14,true)
	local sw=self.w or 16
	w*=0.1875*sw
	s=s or self.spr
	-- todo: bench
	local sx,sy=shl(s,3)%128,shl(flr(s/16),3)
	sspr(sx,sy,sw,sw,x-w/2,y-w/2,w,w)
	palt()
end

function make_plyr(p,angle)
	local model,q=all_models["205gti"],make_q(v_up,angle or 0)
	local brake,turn,traction,traction_ratio,rpm,max_rpm,rpm_decay=0,0,0,0,0,96,0
	local bbox_hits={}
	
	local add_tireforce=function(self,offset,right,fwd,brake,rpm,sensor)
		-- force to world
		right=m_x_v(self.m,right)
		fwd=m_x_v(self.m,fwd)
		
		-- application point (world space)
		local pos,slide=v_clone(self.pos),false
		v_add(pos,m_fwd(self.m),offset)

		-- point velocity
		local relv=self:pt_velocity(pos)
		local relv_len=v_dot(relv,relv)
		-- slip angle
		local sa,sa_ratio=0,1
		if relv_len>k_small then
			--
			sa=-v_dot(right,relv)
			
 		-- make sure to keep velocity
 		-- to compute adjust ratio
 		local t=abs(sa)/12
			-- plyr.slip_angles[sensor]=t
			sa_ratio=apply_curve(sa_curve,t)
		end	
		
		-- long. slip
		relv_len=v_dot(fwd,relv)
		-- convert rpm to rps
		local sr=brake*(rpm and 0.3*rpm or relv_len)-relv_len
		if abs(relv_len)>k_small then
			sr/=abs(relv_len)
		end
		local sr_ratio=sa_ratio*apply_curve(sr_curve,abs(sr))
		-- todo: include speed
		if traction_ratio>0.5 and sr_ratio<0.75 then
			slide=true
		end
		-- todo: include terrain quality
		-- plyr.slip_ratio[sensor]=abs(sr)
				
		-- adjust long
		-- 12: 4wd
		-- 24: 2wd
		sr*=24*sr_ratio

		-- limit overall enveloppe
		sa*=6*sr_ratio
		
		-- impulse factors
		sa*=traction_ratio
		if abs(sa)>k_small then
			v_scale(right,sa)
			self:add_impulse(right,pos)
		end
		
		sr*=traction_ratio
		if abs(sr)>k_small then
			v_scale(fwd,sr)
			self:add_force(fwd,pos)
		end
	
		if slide then
			pos=v_clone(pos)
			v_add(pos,m_right(self.m),rnd(2)-1)
			--add(pos,v_up)
			make_part("smoke",pos)
		end

		return sr_ratio*traction_ratio
	end

	local a={
		mass=32,
		hardness=0.02,
		pos=v_clone(p),
		q=q,
		-- init orientation
		m=m_from_q(q),
		-- obj to world space
		pt_toworld=function(self,p)
			p=m_x_v(self.m,p)
			v_add(p,self.pos)
			return p
		end,
		draw=function(self)
			draw_model(model,self.m,self.pos)
		end,
		draw_shadow=function(self)
			draw_model_shadow(model,self.m,self.pos)
		end,
		control=function(self)
			local angle=0
			if(btn(0)) angle=1
			if(btn(1)) angle=-1

		--[[
			local z=0
			if(btn(2)) z=-1
			if(btn(3)) z=1
			plyr.pos[1]-=turn/4
			plyr.pos[3]+=z/4
		]]
		
			turn+=0.1*angle
			-- brake (full lock:0)
			if btn(3) then
				brake=max(brake-0.1)
			else
				brake=1
			end
			-- accelerate
			if btn(2) then
				rpm=min(rpm+6,max_rpm)
			end
		
			-- steering angle
			angle=1-0.05*turn
			-- debug
			self.angle=angle
			
			-- front wheels
			local c,s=cos(angle),sin(angle)
			rpm_decay=add_tireforce(self,1,{c,0,-s},{s,0,c},brake,nil,1)
			-- rear wheels
			rpm_decay*=add_tireforce(self,-1.2,v_right,v_fwd,btn(5) and 0 or brake,rpm,2)
		end,
		update=function(self)
			traction+=self:up_ratio()
			traction_ratio=traction/5
			
			-- time decay
			traction*=0.2
			turn*=0.92
			rpm*=lerp(0.97,0.95,rpm_decay)
			
			self.rpm_ratio=rpm/max_rpm

			-- sound
			local speed=rpm*(0.8+0.2*rnd())
			local sspd = speed*2
			if (sspd>=1) sspd=speed*1.2
			if (sspd>=1) sspd=speed*0.7
			if (sspd>=1) sspd=speed*0.49
			sspd=sspd%1+speed/16
			poke(0x3200, sspd*4)
			poke(0x3202, sspd*4)

 		if rnd()>0.9 then
 			local pos=self:pt_toworld({0,0,-1.8})
 			--add(pos,v_up)
 			make_part("fire",pos)
 		end
		
			return true
		end
	}
	-- wrap actor with a rigid body facet
	return add(actors,make_rigidbody(a,all_models["205gti_bbox"]))
end

function make_ghost()
	local model,k,best,hist,m=all_models["205gti"],1,{},{}
	-- listen to track event
	on_new_lap=function(t,best_t)
		-- new best?
		if t<=best_t then
			best,hist=hist,{}
		end
		-- restart replay
		k=1
	end
	
	return add(actors,{
		pos=v_zero(),
		q=make_q(v_up,0),
		draw=function(self)
		 if m then
				draw_model(model,m,self.pos,true)
			end
		end,
		is_active=function() return m end,
		update=function(self)
			if time_t%2==0 then
				-- capture current pos
				serialize(plyr.pos,hist)
				serialize(plyr.q,hist)
				-- replay best track
				local n=#best
				if n>0 then
					k=deserialize(best,k,self.pos)
					k=deserialize(best,k,self.q)
					-- update model matrix
					m=m_from_q(self.q)
					-- loop
					if(k>n) k=1
				end
			end
			return true
		end
	})
end

-- note: limited to a single actor per tile
local all_ground_actors={
	-- checkpoint
	{spr=35,hit_part="chkpt"},
	-- cone
	{spr=53,hit_part="cone",w=8},
	-- tree/random props
	{rnd={spr={96,108,108}},hit_part="tree"},
	-- lil'people
	{rnd={spr={66,68,98,33}},hit_part="angel",hit_t=150},
}
function make_ground_actor(i,j,kind)
	local x,z,idx=shl(i+rnd(),ground_shift),shl(j+rnd(),ground_shift),safe_index(i,j)
	local a=clone(all_ground_actors[kind],{
		pos={x,get_altitude_and_n({x,0,z})+0.5,z},
		idx=idx,
		draw=ssprt
	})
	ground_actors[idx]=a
	return a
end

-- creates a collision solver for:
-- body
-- normal
-- body contact point (world position)
-- penetration
function is_contact(a,p,n,d)
	local padot=a:pt_velocity(p)
	local vrel=v_dot(n,padot)
	-- resting condition?
	if(d<k_small and vrel>-k_small_v) return
 return true
end
function make_contact_solver(a,p,n,d)
	local nimpulse=0
	local ra=make_v(a.pos,p)
	local racn=make_v_cross(ra,n)

	local nm=a.mass_inv
	nm+=v_dot(racn,m_x_v(a.i_inv,racn))
	nm=1/nm
	
	-- baumgarte
	local bias=-k_bias*max(d+k_slop)/time_dt

	-- restitution bias
	local va=v_clone(a.v)
	v_add(va,make_v_cross(a.omega,ra))
	local dv=-v_dot(va,n)
	-- todo:find out unit??
	if dv<-1 then
		bias-=a.hardness*dv
	end
	
	-- contact solver
	return function()
		local dv,n=v_clone(a.v),v_clone(n)
		v_add(dv,make_v_cross(a.omega,ra))

		local lambda=-nm*(v_dot(dv,n)+bias)
	
		local tempn,nimpulse=nimpulse,max(nimpulse+lambda)
		lambda=nimpulse-tempn
		
		-- impulse too small?
		if(lambda<k_small) return false
		-- correct linear velocity
		v_scale(n,lambda)
		v_add(a.v,n,a.mass_inv)
		-- correct angular velocity
		v_add(
			a.omega,
			m_x_v(
				a.i_inv,
				make_v_cross(ra,n)
			))
		return true
	end
end

-- rigid body extension for a given actor
-- bounding box
function make_rigidbody(a,bbox)
	local force,torque=v_zero(),v_zero()
 -- model bounding box
	local vmin,vmax={32000,32000,32000},{-32000,-32000,-32000}
	for _,v in pairs(bbox.v) do
		vmin,vmax=v_min(vmin,v),v_max(vmax,v)
	end
	
	-- compute inertia tensor
	local size=v_sqr(make_v(vmin,vmax))
	local ibody=make_m(size[2]+size[3],size[1]+size[3],size[1]+size[2])
	m_scale(ibody,a.mass/12)
	
	-- invert 
	local ibody_inv=m_inv(ibody)
	-- 
	local g={0,-24*a.mass,0}
	
	local rb={
		i_inv=make_m(),
		v=v_zero(),
		omega=v_zero(),
		mass_inv=1/a.mass,
		-- world velocity
		pt_velocity=function(self,p)
			p=make_v_cross(self.omega,make_v(self.pos,p))
			v_add(p,self.v)
			return p
		end,
		incident_face=function(self,rn)
			rn=v_clone(rn)
			-- world to local
			m_inv_x_v(self.m,rn)
			local dmin,fmin,nmin=32000
			for _,f in pairs(bbox.f) do
				local n=f.n
				local d=v_dot(rn,n)
				if d<dmin then
					dmin,fmin,nmin=d,f,n
				end
			end
			return fmin,nmin
		end,
			-- register a force
		add_force=function(self,f,p)
			v_add(force,f,a.mass)
			v_add(torque,make_v_cross(make_v(self.pos,p),f))
		end,
		add_impulse=function(self,f,p)
		 
			v_add(self.v,f,self.mass_inv)
			v_add(self.omega,m_x_v(self.i_inv,make_v_cross(make_v(self.pos,p),f)))
		end,
		-- apply forces & torque for iteration
		prepare=function(self,dt)
			-- add gravity
			v_add(force,g)
		
			-- inverse inertia tensor
			self.i_inv=m_x_m(m_x_m(self.m,ibody_inv),m_transpose(self.m))
	
			-- velocity
			v_add(self.v,force,self.mass_inv*dt)
	
			-- angular velocity
			v_add(self.omega,m_x_v(self.i_inv,torque),dt)
			
			-- friction
			v_scale(self.v,1/(1+dt*0.4))
			v_scale(self.omega,1/(1+dt*0.6))
		end,
		integrate=function(self,dt)
			v_add(self.pos,self.v,dt)
			q_dydt(self.q,self.omega,dt)
			self.m=m_from_q(self.q)
			-- clear forces
			force,torque=v_zero(),v_zero()
			-- hit effect
			for _,v in pairs(bbox.v) do
			 -- new contact?
				if v.contact_t and v.contact_t==time_t and (v.last_contact_t==nil or time_t-v.last_contact_t>10) then
				 sfx(11)	
				 break
			 end 
			end
		end,
		update_contacts=function(self,contacts)
			-- ground contacts against incident face
			local f=self:incident_face(v_up)
			local raw_contacts={}
			for _,vi in pairs(f.vi) do
				local v=bbox.v[vi]
				-- to world space
				local p=self:pt_toworld(v)
				local h,n=get_altitude_and_n(p,true)
				local depth=h-p[2]
				if depth>k_small then
					depth=v_dot(n,{0,depth,0})
					-- deep enough?
					if depth>-k_small then						
						if is_contact(self,p,n,depth) then
						 -- find contact by normal
						 local cn=raw_contacts[n] or {v_zero(),v_clone(n),0,0}
					 	v_add(cn[1],p)
					 	v_add(cn[2],n)
	 			 	v_normz(cn[2])
							cn[3]+=depth
							cn[4]+=1	
						 raw_contacts[n]=cn
						 -- record contact time
							v.last_contact_t,v.contact_t=v.contact_t,time_t
							v.n=n
						end
					end
				end
			end
			
			for _,c in pairs(raw_contacts) do
				-- average position
				v_scale(c[1],c[4])				
				add(contacts,make_contact_solver(self,c[1],c[2],c[3]/c[4]))
			end
						
			-- hit ground actors?
			for _,a in pairs(active_ground_actors) do
				local v=plyr:is_colliding(a.pos)
				if v then
					-- make it fly a bit!
					v[2]+=2+rnd(3)
					make_part(a.hit_part,a.pos,v)
					-- shake car
					self:add_force({0,96+rnd(32),0},a.pos)
					-- penalty time?
					if(a.hit_t) track:penalty(a.hit_t)
					-- kill actor
					ground_actors[a.idx]=nil
				end
			end
		end,
		-- is rigid body on ground?
		up_ratio=function(self)
			local r,up=0,m_up(self.m)
			for i=1,4 do
				local v=bbox.v[i]
				if v.contact_t and time_t-v.contact_t<5 then
					-- contact quality
					r+=max(v_dot(up,v.n))
				end
			end
			return r
		end,
		-- return if point p is colliding with rigidbody bbox
		-- returns relative velocity of impact
		is_colliding=function(self,p)
			if(sqr_dist(self.pos,p)>12) return
			-- world to obj space
			p=make_v(self.pos,p)
			m_inv_x_v(self.m,p)
			for _,f in pairs(bbox.f) do
				-- front facing: no collision
				if(v_dot(f.n,p)>=f.cp) return
			end
			-- relative velocity
			p=make_v_cross(self.omega,p)
			v_add(p,self.v)
			return p
		end
	}
	
	-- register rigid bodies
	return add(physic_actors,clone(rb,a))
end

-- physic world
function world:update()
	local contacts={}
	for _,a in pairs(physic_actors) do
		-- collect contacts
		a:update_contacts(contacts)
		a:prepare(time_dt)
	end
	
	-- solve contacts
	for _,c in pairs(contacts) do
		-- multiple iterations
		-- required to fix deep contacts
		for i=1,5 do
			if(c()==false) break
		end
	end
	
	-- move bodies
	for _,a in pairs(physic_actors) do
		a:integrate(time_dt)
	end
end

-- track
-- best lap time to beat
function make_track(best_t,segments)
	-- "close" track
	add(segments,segments[1])
	-- active index
	local checkpoint,free_t=0,30
	-- lap_time
	-- remaining time before game over (+ some buffer time)
	local lap_t,remaining_t=0,best_t+free_t
	return {	
		get_best_t=function()
			return best_t
		end,
		get_startpos=function(self)
			return segments[1].pos
		end,
		-- returns next location angle,pos
		get_dir=function(self,pos)
			local p=segments[checkpoint+1].pos
			local v=make_v(pos,p)
			return (atan2(v[1],v[3])+1)%1,p
		end,
		-- time penalty
		penalty=function(self,t)
			lap_t+=t
		end,
		update=function(self)
			remaining_t-=1
			if remaining_t==0 then
				next_state(gameover_state)
				return
			end
			lap_t+=1
			local p=segments[checkpoint+1]
			if sqr_dist(plyr.pos,p.pos)<64 then
				checkpoint+=1
				sfx(7)
				if checkpoint%#segments==0 then
					checkpoint=0
					if(lap_t<best_t) then
						best_t=lap_t
						-- a bit more challenging!
						free_t/=2
						-- save to cart data
						dset(0,best_t)
					end
					-- notify ghost
					on_new_lap(lap_t,best_t)
					-- next time
					lap_t,remaining_t=0,best_t+free_t
				end
			end
		end,
		draw=function(self)
			-- lap time
			printb("⧗"..time_tostr(lap_t),2,2,7)
			-- best time
			printb("★"..time_tostr(best_t),2,8,10)
	
			-- count down when below 10s
			if remaining_t<=300 then
				pal(7,8)
				-- bip
				if(remaining_t%30==0) sfx(1)
			end
			sprint(padding(flr(remaining_t/30)),60,2,21,2)
			pal()
			
			local angle,p=self:get_dir(plyr.pos)
			print_dist("",p,dist,0.5,7)
			
			if ghost and ghost:is_active() then
				print_dist("░",ghost.pos,dist,12,10)
			end
		end
	}
end

-- camera
function make_cam(focal)
	-- camera rotation
	local cc,ss=1,0
	local dist=shl(8,ground_shift)
	return {
		pos={0,6*hscale,0},
		lookat={0,0,-7*16},
		track=function(self,pos,angle,d)
			dist=lerp(dist,d,0.1)
			self.pos=v_clone(pos)
			self.lookat=v_clone(pos)
			cc,ss=cos(angle),-sin(angle)
			v_add(self.pos,{0,dist*ss,dist*cc})
		end,
		project=function(self,v)
			-- pitch 
			local x,y,z=v[1]-self.lookat[1],-self.lookat[2],v[3]-self.lookat[3]
			z,y=cc*z+ss*y,-ss*z+cc*y

			local ze=z-dist

			local w=-focal/ze
  			return 63.5+x*w,63.5-(v[2]+y)*w,ze,w
		end
	}
end

-- particles
function update_part(self)
	if(self.t<time_t) return false
	-- gravity
	v_add(self.v,v_grav,self.g_scale)
	-- update pos
	local p=self.pos
	v_add(p,self.v,0.1)
	-- ground collision
	local h=get_altitude_and_n(p)
	if p[2]<h then
		p[2]=h
		-- crude reflection
		v_scale(self.v,0.8)
	end
	
	-- force damping
	v_scale(self.v,self.dv or 0.9)
	
	-- animation frame
	self.frame+=self.df
	
	return true
end

function draw_part(self)
	local n,s=#self.frames
	if self.kind==0 then
		s=self.frames[flr(self.frame*(n-1))+1]
	elseif self.kind==1 then
		s=self.frames[flr((self.frame*(n-1))%n)+1]
	end
	ssprt(self,s)
end

function draw_part_shadow(self)
	local x,y,z,w=cam:project({self.pos[1],get_altitude_and_n(self.pos),self.pos[3]})
	-- behind camera
	if(z>=0) return
	
	spr(37,x-4,y)
end

all_parts={	  
    smoke={
    	sfx=10,
        frames={
            64,
            80,
            81,
            65
        },
        rnd={
            dly={
                8,
                12
            },
            g_scale={
                -0.03,
                -0.05
            }
        },
        kind=0,
        w=8
    },
    fire={
        frames={22,38,54},
        rnd={
			         dly={3,6}
        },
        g_scale=0,
        kind=0,
        w=8
    },
    chkpt={
    				sfx=9,
        draw_shadow=draw_part_shadow,
        frames={3},
        rnd={
            dly={
                30,
                60
            }
        },
        kind=1
    },
    tree={
    				sfx=9,
        draw_shadow=draw_part_shadow,
        frames={
            70
        },
        rnd={
            dly={
                24,
                32
            }
        },
        kind=1,
        w=8
    },
    angel={
    				sfx=8,
        draw_shadow=draw_part_shadow,
        frames={
            110
        },
        rnd={
            dly={
                30,
                60
            }
        },
        kind=1,
        w=16,
        g_scale=-0.3
    },
    cone={
    		sfx=6,
     	draw_shadow=draw_part_shadow,
        frames={
            100,
            101,
            102,
            103,
            104,
            105,
            106,
            107
        },
        rnd={
            dly={
                70,
                90
            }
        },
        kind=1,
        w=8
    }
}

function make_part(part,p,v)
	local pt=add(parts,clone(all_parts[part],{pos=v_clone(p),v=v and v_clone(v) or v_zero(),frame=0,draw=draw_part,update=update_part}))
	pt.t=time_t+pt.dly
	pt.df=1/pt.dly
	if(pt.sfx) sfx(pt.sfx)
	return pt
end

-- map helpers (marching codes, height map, normal map cache)
local qmap,hmap={},{}
function safe_index(i,j)
	return bor(band(i,0x7f),shl(band(j,0x7f),7))
end
function get_raw_qcode(i,j)
	return qmap[safe_index(i,j)] or 0
end
function get_height(i,j)
	return hmap[safe_index(i,j)] or 0
end

-- return altitude & normal (optional)
function get_altitude_and_n(v,with_n)
	-- cell
	local x,z=v[1],v[3]
	local dx,dz=shr(x%ground_scale,ground_shift),shr(z%ground_scale,ground_shift)
	local i,j=flr(shr(x,ground_shift)),flr(shr(z,ground_shift))
	local h0,h1,n
	if dx>dz then
		local h=get_height(i,j)
		h0,h1=lerp(h,get_height(i+1,j),dz),lerp(h,get_height(i+1,j+1),dx)
		if with_n then
			n=make_v_cross(
				{ground_scale,get_height(i+1,j+1)-h,ground_scale},
				{ground_scale,get_height(i+1,j)-h,0})
			v_normz(n)
		end
	else
		local h=get_height(i+1,j+1)
		h0,h1=lerp(get_height(i,j),h,dz),lerp(get_height(i,j+1),h,dx)
		if with_n then
			n=make_v_cross(
				{0,get_height(i,j+1)-h,ground_scale},
				{ground_scale,get_height(i+1,j+1)-h,ground_scale})
			v_normz(n)
		end
	end
	return lerp(h0,h1,dz),n
end

-- draw actors on strip j
function draw_actors(j)
	local bucket=zbuf[band(j-1,0x7f)]
	if bucket then
		-- shadow pass
		for _,d in pairs(bucket) do
			d=d.obj
			-- draw shadow
			if (d.draw_shadow) d:draw_shadow()
		end
		for _,d in pairs(bucket) do
			d=d.obj
			d:draw()
		end
	end
end

function update_ground()
	local pos=plyr and plyr.pos or cam.lookat
	local i0,j0=flr(shr(pos[1],ground_shift)),flr(shr(pos[3],ground_shift))
	-- clear active list
	active_ground_actors={}
	for i=i0+ground_left,i0+ground_right do
		local cx=band(i,0x7f)
		for j=j0+ground_near,j0+ground_far do
			local cy=band(j,0x7f)
			local t=ground_actors[cx+shl(cy,7)]
			if t then
				add(active_ground_actors,t)
				add(drawables,t)
			end
		end
	end
end

local shade=function(c)
	return bor(shl(sget(16,c),4),sget(17,c))
end

function draw_ground()
	local cx,cz=cam.lookat[1],cam.lookat[3]
	-- cell x/z ratio
	local dx,dz=cx%ground_scale,cz%ground_scale
	-- cell coordinates
	local nx,ny=flr(shr(cx,ground_shift)),flr(shr(cz,ground_shift))
	
	-- project anchor points
	local p,xmin={},shl(ground_left,ground_shift)-dx+cx
	-- grid depth extent
	for j=ground_near,ground_far do
	 -- project leftmost grid points
		local x,y,z,w=cam:project({xmin,0,-dz+cz+shl(j,ground_shift)})
		add(p,{x,y,z,w,ny+j})
	end
	
	-- move to 0-1 range
	dx/=ground_scale
	dz/=ground_scale
	
	local v0=p[1]
	local w0,nj=v0[4],v0[5]
	local dw0=shl(w0,ground_shift)
	for j=2,#p do
		-- offset to grid space
		local ni=nx+ground_left
		local i,di=ground_left,1
		
		local v1=p[j]
		local w1=v1[4]
		local dw1=shl(w1,ground_shift)
		local x0,x1=v0[1],v1[1]
		
		-- todo: unit for w?
		local h0,h1=get_height(ni,nj),get_height(ni,nj+1)
		local y0,y1=v0[2]-w0*h0,v1[2]-w1*h1
		local q0=get_raw_qcode(ni,nj)
		while i<=ground_right do
			local q3=get_raw_qcode(ni+1,nj)
			-- detail tile?
			if i==ground_left or i>=ground_right-1 or ni%2==1 or q0!=q3 then
				di=1
			else
				di=2
				q3=get_raw_qcode(ni+2,nj)
			end
			local x2,x3=x1+di*dw1,x0+di*dw0
			local h2,h3=get_height(ni+di,nj+1),get_height(ni+di,nj)
			local y2,y3=v1[2]-w1*h2,v0[2]-w0*h3

			-- in screen tile?
			if x3>0 then
				-- left/right cliping
				if i==ground_left then
					x0,y0=lerp(x0,x3,dx),lerp(y0,y3,dx)
					x1,y1=lerp(x1,x2,dx),lerp(y1,y2,dx)
				elseif i==ground_right then
					x3,y3=lerp(x0,x3,dx),lerp(y0,y3,dx)
					x2,y2=lerp(x1,x2,dx),lerp(y1,y2,dx)
				end

				-- backup values
				local xx0,yy0,xx3,yy3=x0,y0,x3,y3
				local xx1,yy1,xx2,yy2=x1,y1,x2,y2
				-- depth cliping
				if j==2 then
					x0,y0=lerp(x0,x1,dz),lerp(y0,y1,dz)
					x3,y3=lerp(x3,x2,dz),lerp(y3,y2,dz)
				elseif j==#p then
					x1,y1=lerp(x0,x1,dz),lerp(y0,y1,dz)
					x2,y2=lerp(x3,x2,dz),lerp(y3,y2,dz)
				end
				
				local c_hi,c_lo=shade(shr(band(0b00111000,q0),3)),shade(band(0b111,q0))

				fillp(dither_pat2[shr(band(ni,2)+band(nj,2),1)+1])

				-- single color quad?
				if c_hi==c_lo then
					polyfill({{x0,y0},{x1,y1},{x2,y2},{x3,y3}},c_hi)
				else
					-- boundary triangles
					if band(q0,0x40)>0 then
						polyfill({{x0,y0},{x2,y2},{x1,y1}},c_hi)
						polyfill({{x0,y0},{x2,y2},{x3,y3}},c_lo)
					else
						polyfill({{x1,y1},{x3,y3},{x0,y0}},c_lo)
						polyfill({{x1,y1},{x3,y3},{x2,y2}},c_hi)
					end
				end

				-- restore values (for clipping)
				x0,y0,x3,y3=xx0,yy0,xx3,yy3
				x1,y1,x2,y2=xx1,yy1,xx2,yy2
			end
					
			-- no need to go further, tile is not visible
			if(x0>127) break
			x0,y0,x1,y1=x3,y3,x2,y2
			h0,h1=h3,h2
			q0=q3

			ni+=di
			i+=di
		end
		
		fillp()
		draw_actors(nj)
		
		v0,w0,dw0=v1,w1,dw1
		nj+=1
	end
	-- last strip
	draw_actors(nj)
end

--[[
local dither_pat={0b1111111111111111,0b0111111111111111,0b0111111111011111,0b0101111111011111,0b0101111101011111,0b0101101101011111,0b0101101101011110,0b0101101001011110,0b0101101001011010,0b0001101001011010,0b0001101001001010,0b0000101001001010,0b0000101000001010,0b0000001000001010,0b0000001000001000,0b0000000000000000}
function draw_ground()
	local cx,cz=cam.lookat[1],cam.lookat[3]
	-- cell x/z ratio
	local dx,dz=cx%ground_scale,cz%ground_scale
	-- cell coordinates
	local nx,ny=flr(shr(cx,ground_shift)),flr(shr(cz,ground_shift))
	
	-- project anchor points
	local p,i={},nx
	local xmin,xmax,zmin,zmax=cx+shl(ground_left,ground_shift),cx+shl(ground_right-2,ground_shift),cz+shl(ground_near,ground_shift),cz+shl(ground_far-2,ground_shift)
	for ii=ground_left,ground_right do
		local row={}
		for jj=ground_near,ground_far do
			local x,y,z,w=cam:project({
			mid(shl(ii,ground_shift)-dx+cx,xmin,xmax),
			get_height(ii+nx,jj+ny),
			mid(shl(jj,ground_shift)-dz+cz,zmin,zmax)})
			add(row,{flr(x),flr(y),w,get_raw_qcode(ii+nx,jj+ny),nx+ii,ny+jj})
		end
		add(p,row)
	end

	local r0=p[1]
	for j=2,#p do
		local r1=p[j]
		local v0,v3=r0[1],r1[1]
		local x0,y0,x3,y3=v0[1],v0[2],v3[1],v3[2]
		local q0,w0=v0[4],v0[3]
		for i=2,#r1 do
			local v1,v2=r0[i],r1[i]
			local x1,y1,x2,y2=v1[1],v1[2],v2[1],v2[2]
			local q1,w1=v1[4],v1[3]
			
			local c_hi,c_lo,c_dither=shr(band(0b00111000,q0),3),band(0b111,q0)

			local ni,nj=v0[5],v0[6]
			local strip=(nj%4<2) and 0 or 1
			strip+=((ni%4<2) and 0 or 1)
			c_hi,c_lo=shade(1,c_hi),shade(1,c_lo)

			fillp(dither_pat2[strip+1])
			
			if c_hi>=1 or c_lo>=1 then
				if band(q0,0x40)>0 then
					trifill(x0,y0,x2,y2,x1,y1,c_hi)
					trifill(x0,y0,x2,y2,x3,y3,c_lo)
				else
					trifill(x1,y1,x3,y3,x0,y0,c_lo)
					trifill(x1,y1,x3,y3,x2,y2,c_hi)
				end
			end
			v0,v3,q0=v1,v2,q1
			x0,y0,x3,y3=x1,y1,x2,y2
			w0=w1
		end
		r0=r1
	end
	fillp()
end
]]

-- game states
-- transition to next state
function next_state(state)
	draw_state,update_state=state()
end

function start_state()
	-- reset arrays & counters
	time_t,actors,ground_actors,parts,active_ground_actors=0,{},{},{},{}

	-- read track
	local prev_best_t=dget(0)
	-- safe value
	if(prev_best_t<=0) prev_best_t=4500
	track=make_track(prev_best_t,unpack_track())

	-- read actors
	unpack_array(function()
		make_ground_actor(2*unpack_int(),2*unpack_int(),unpack_int())
	end)

	local pos=track:get_startpos()
	-- create player in correct direction
	plyr=make_plyr({pos[1],pos[2]+4,pos[3]},track:get_dir(pos))

	-- debug
	--plyr.slip_angles={0,0}
	--plyr.slip_ratio={0,0}

	
	local ttl=120
	return 
		-- draw
		function()
			local t=flr(ttl/30)
			banner(0x12)
			local x=t==0 and 50 or 60
			sprint(t==0 and "go!" or tostr(t),x,46,21,2)	
		end,
		-- update
		function()
			if(ttl%30==0) sfx(ttl<=30 and 2 or 1)
			ttl-=1
			if(ttl<0) next_state(play_state)
		end
end

function play_state()
	-- remaining lifts
	local lifts,lift_ttl,lift_y=3,-1,-12

	-- init ghost
	ghost=make_ghost()

	return
		function()
			if lift_ttl>0 then
				local x0,y0=cam:project(plyr.pos)
				line(x0,0,x0,y0-16,7)
				spr(31,x0-3,y0-16)

				lift_y=lerp(lift_y,2,0.1)

				spr(47,110,lift_y)
				printb(tostr(lifts),115,lift_y,7)
			end

			draw_hud()
		end,
		-- update
		function()
			lift_ttl-=1

			if plyr then
				track:update()
				plyr:control()
	
				-- trigger light
				if lift_ttl<0 and lifts>0 and btnp(4) then
					lifts-=1
					lift_ttl=60
					lift_y=-12
				end

				-- grab car!
				if lift_ttl>0 then
					local pos=v_clone(plyr.pos)
					v_add(pos,m_up(plyr.m),3)
					local force=v_clone(v_up)
					v_scale(force,30)
					plyr:add_force(force,pos)
				end
			end
		end
end

function gameover_state()
	local ttl=900
	return 
		-- draw
		function()
			banner(0x82)
			sprint("game over",35,46,21,2)
			rectfill(0,59,127,65,2)
			?"best time:"..time_tostr(track:get_best_t()),36,60,10

			?"press ❎/🅾️ to continue",24,110,ttl%2==0 and 7 or 11
		end,
		-- update
		function()
			ttl-=1
			if btnp(4) or btnp(5) or ttl<0 then
				next_state(start_state)
			end
		end
end

function _update()
	time_t+=1

	-- basic state mgt
	update_state()
	
	zbuf_clear()
	
 	-- update active ground objects	
	update_ground()
	
	-- physic update
	world:update()
	
	-- game logic update
	zbuf_filter(actors)
	zbuf_filter(parts)
	
	if plyr then
		-- update cam
		local lookat=v_clone(plyr.pos)
		v_add(lookat,m_fwd(plyr.m),3)
		-- keep altitude
		lookat[2]=plyr.pos[2]+2
		cam:track(lookat,0.15,lerp(8,16,plyr.rpm_ratio))
	end
end

function padding(n)
	n=tostr(flr(min(n,99)))
	return sub("00",1,2-#n)..n
end

function time_tostr(t)
	if(t==32000) return "--"
	-- frames per sec
	local s=padding(flr(t/30)%60).."''"..padding(flr(10*t/3)%100)
	-- more than a minute?
	if(t>1800) s=padding(flr(t/1800)).."'"..s
	return s
end

-- print box
function printb(s,x,y,c)
	?s,x,y+2,1
	?s,x,y+1,5
	?s,x,y,c
end

function banner(c,t)
	local x=48*smoothstep(t and 1-t or 0)
	rectfill(x,44,127-x,59,c)
	fillp(0xa5a5)
	rectfill(x,45,127-x,58,c)
	fillp()
end

function draw_gauge()
	circ(16,111,16,7)
	local i,di,c=0.75,-0.1,7
	while i>0 do
		pset(16+13.5*cos(i),111+13.5*sin(i),c)
		if(i<0.2) di=-0.025 c=8
		i+=di
	end
	local rpm=1-plyr.rpm_ratio
	rpm*=0.75
	color(8)
	line(16,111,15+10*cos(rpm),111+10*sin(rpm))
	circfill(16,111,3)
end

function draw_hud()
	camera(0,-1)
	memset(0x5f00,0x1,16)
	draw_gauge()
	camera()
	pal()
	draw_gauge()
	
	track:draw()
end

--[[
function draw_curve(s,x,y,t,curve)
	local h=y+24
	rectfill(x,y,x+32,h,1)
	print(s..":"..t,x+1,y+1,7)
	for i=0,32 do
		pset(x+i,h-16*apply_curve(curve,i/32),13)
	end
	t=min(abs(t),1)
	line(x+32*t,y+6,x+32*t,h,8)
end
]]

function _draw()
	cls(0)

	zbuf_sort()
	draw_ground()
	
	draw_state()
	
	--[[
	local p=ghost.pos
	print(flr(p[1]).."/"..flr(p[2]).."/"..flr(p[3]),90,2,7)
	]]

	--[[	
	draw_curve("f.sa",1,20,plyr.slip_angles[1],sa_curve)
	draw_curve("r.sa",1,46,plyr.slip_angles[2],sa_curve)
	
	draw_curve("f.sr",94,20,plyr.slip_ratio[1],sr_curve)
	draw_curve("r.sr",94,46,plyr.slip_ratio[2],sr_curve)
	]]
	
	--[[	
	if plyr.angle then
		print((plyr.angle-1)*360,2,74,7)
	end	
	]]

 	-- rectfill(0,0,127,8,8)
	--print(solver_i/solver_n,2,1,1)
	-- print("mem:"..stat(0).." cpu:"..stat(1).."("..stat(7)..")",2,2,7)
 
 	--print(plyr.acc,2,18,7) 
end

function _init()
	cartdata("freds2_ghost_rally")

	sfx(0,3,0)
	-- q binary layout
	-- 0b01000000: rle bit
	-- 0b01000000: q code
	-- 0b00111000: hi color
	-- 0b00000111: lo color
		
	-- read models from gfx/map data
	unpack_models()
	
	-- unpack curves from sfx data
	sa_curve,sr_curve=unpack_curve(4),unpack_curve(5)

	-- unpack map
	local i=0
	unpack_rle(function(v)
		qmap[i]=v
		i+=1
		return i<0x4000
	end)
	i=0
	local tmp_hmap={}
	unpack_rle(function(v)
		tmp_hmap[i],tmp_hmap[i+1]=shr(band(0xf0,v),4),band(0xf,v)
		-- lower heightmap
		tmp_hmap[i]/=2
		tmp_hmap[i+1]/=2
		i+=2
		return i<0x1000
	end)
	-- linear lerp to 128x128
	for j=0,62 do
		for i=0,62 do
			local idx=i+64*j
			local h0,h1,h2,h3=tmp_hmap[idx],tmp_hmap[idx+64],tmp_hmap[idx+65],tmp_hmap[idx+1]
			idx=2*i+256*j
			hmap[idx]=h0
			hmap[idx+1]=(h0+h3)/2
			hmap[idx+128]=(h0+h1)/2
			hmap[idx+129]=(h0+h1+h2+h3)/4
		end
	end
		
	cam=make_cam(95.5)
		
	-- init state machine
	next_state(start_state)
end

-->8
-- unpack models & data
local mem=0x1000
function unpack_int()
	local i=peek(mem)
	mem+=1
	return i
end
function unpack_float(scale)
	local f=(unpack_int()-128)/32	
	return f*(scale or 1)
end
-- valid chars for model names
local itoa='_0123456789abcdefghijklmnopqrstuvwxyz'
function unpack_string()
	local s=""
	unpack_array(function()
		local c=unpack_int()
		s=s..sub(itoa,c,c)
	end)
	return s
end
function unpack_array(fn)
	for i=1,unpack_int() do
		fn(i)
	end
end
function unpack_models()
	-- for all models
	unpack_array(function()
		local model,name,scale={v={},f={}},unpack_string(),unpack_int()
		-- vertices
		unpack_array(function()
			add(model.v,{unpack_float(scale),unpack_float(scale),unpack_float(scale)})
		end)
		
		-- faces
		unpack_array(function(i)
			local f={ni=i,vi={},uv={}}
			-- vertex indices
			unpack_array(function()
				add(f.vi,unpack_int())
			end)
			-- uv coords (if any)
			unpack_array(function()
				add(f.uv,{u=unpack_int(),v=unpack_int()})
			end)
			-- center point
			f.center={unpack_float(scale),unpack_float(scale),unpack_float(scale)}
			add(model.f,f)
		end)

		-- normals
		unpack_array(function(i)
			model.f[i].n={unpack_float(),unpack_float(),unpack_float()}
		end)
		
		-- n.p cache
		for _,f in pairs(model.f) do
			f.cp=v_dot(f.n,model.v[f.vi[1]])
		end
	
		-- merge with existing model
		all_models[name]=clone(model,all_models[name])
	end)
end
function unpack_rle(decode)
	local read=true
	while read do
		-- peek data
		local k,q=unpack_int()
		-- rle or value?
		if band(0x80,k)>0 then
		-- run length
			k,q=band(0x7f,k),unpack_int()
		else
			k,q=1,k
		end
		for j=1,k do
			read=decode(q)
		end
	end
end
-- unpack int array
local mem_track
function unpack_track()
	if mem_track then
		mem=mem_track
	else
		mem_track=mem
	end
	local track={}
	unpack_array(function()
		-- +1 shift to center track marker
	 	local pos={shl(unpack_int()+1,ground_shift+1),0,shl(unpack_int()+1,ground_shift+1)}
		pos[2]=get_altitude_and_n(pos)
		add(track,{pos=pos})
	end)
	return track
end
-- unpack curve from sfx
function unpack_curve(sfx)
	local bytes={}
 local addr=0x3200+68*sfx
 for k=1,16 do
 	local note=peek4(addr)
		add(bytes,band(shl(note,16),0x3f))
		add(bytes,band(note,0x3f))
 	addr+=4
 end	
	return bytes
end
-->8
-- polygon renderers
#include polyfill.lua
#include polytex.lua

-->8
-- print helpers
-- sprite print
local bprint_chars=" ▒0123456789-abcdefghijklmnopqrstuvwxyz!"
local chars2mem={}
for i=1,#bprint_chars do
	local c=sub(bprint_chars,i,i)
	cls(0)
	?c,0,0,7
	local mem=0x4300+shl(i-1,5)
	for y=0,7 do
		memcpy(mem+4*y,0x6000+shl(y,6),4)
	end
	chars2mem[c]=mem
end
	
function sprint(txt,x,y,...)
	palt(0,false)
	palt(14,true)
	do_sprint(txt,x,y+1,...)
	-- pal(7,7)
	-- do_sprint(txt,x,y,...)
	pal()
end

function do_sprint(txt,x,y,s,w)
	for i=1,#txt do
		local mem=chars2mem[sub(txt,i,i)]
		local xmax=0
		for j=0,5 do
			local mask=peek4(mem)
			for k=0,7 do
				if band(mask,0x.000f)!=0 then
					-- glyph support
					if(k>xmax) xmax=k
					spr(s,x+k*w,y+j*w)
				end
				mask=shr(mask,4)
			end
			mem+=4
		end
		--next char
		x+=w*(xmax+2)
	end
end

function print_dist(name,p,dist,max_dist,c)
	local dist=v_xz_dist(make_v(p,plyr.pos))
	if dist>max_dist then
		local s=name..flr(dist).."m"
		local x,y=cam:project(p)
		printb(s,mid(x,0,127-5*#s),mid(y,32,120),c)
	end
end


__gfx__
00000000000151003b000000eeeeeeeeeeeeeeee9aa79000eeeeeeeebb88856599777777777777777777777777777777777777788756566bb000000000777000
0000000001dc770024000000eeeeeeeeeeeeeeee9aa79000ee7777eeb888856599766666777777777711666667666677777777788756666bb000000007666700
0070070012e7770049000000eeeeee7eee56eeee9aa79000e7eeee7eb8888565657666667777777777116666677777666666667aa756776bb000000006666600
000770003333b70013000000eeee7777ee66eeee09790000e7e7ee7eb8888565657666667777777777116666677777777777776aa756776bb000000000666000
000770002497a70024000000eee777766eeeeeee00900000e7e77e7ebb0555656586666677777777771166666777777887667765a756776bb000000000666000
0070070015d7670015000000ee7777565eeeeeee9aa79000e7eeee7ebb0555656c866666777777777711666665777788877766656756556bb000000000060000
000000001567670054000000ee57655556eeeeee00000000ee7777eebb505565cc866666777777777711666665777780877777656756666bb000000001060100
000000001556670067000000eee6565655eeeeee00000000eeeeeeeebb055565cc866666777777777711666665777787877777656756556bb000000010101010
1ca9b3452288ee0028000000eee56565566eeeee77eeeeeeeeeeeeeebb505565ca766666777777777711666665777788877777656756666bb000000000000000
00000000499ffa0054000000eeee55556e56eeee77eeeeeeeeeeeeeebb056565aa766666777777777711666665777778877777656756556bb000000000060000
4950000099aaa7009a000000eeeee566ee6eeeeeeeeeeeeeeee898eebb566565a1766666777777777711666665777777777777765756666bb000000000576000
0000000055533b003b000000eeeeeeeeeeeeeeeeeeeeeeeeee8a79eebb50656511766666777777777711666665777777778877567756556bb000000000050000
7a9420001dcc7c001c000000eeeeeee5e56eeeeeeeeeeeeeee8979eebb56656511766666777777777711666665777778888877656756666bb000000000060000
7e882000115dd6001d000000eeeeeeeee6eeeeeeeeeeeeeeeee898eebb05656518766666777777777711666665777788111177656756556bb000000000007000
777770001122ee002e000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeebb5055658876666677777777771166666577778111aa77656756666bb000000007006000
76d5d00022eeff00ef000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeebb05556585788666777777777711666665777781aacc77656756556bb000000000660000
00000000eeeeeeeeeeeeeeeeeeeee777777eeeee01010100eeeeeeeebb50556565788866777777777711666665777781acc777656756666bb000000007000000
00000000eeeeeeeeeeeeeeeeeeeee777777eeeee10101010eeeeeeeebb05556565780866777777777711666665777781ac7766656756556bb000000077700000
00100100eeeeeeeeeeeeeeeeeeeee777777eeeee01010100eeeeeeeebb05556565787866777777777711666667777781a7667765a756776bb000000017100000
00000000eeeeeeeeeeeeeeeeeeeee665566eeeee00000000eee9aeeeb8888565657888667777777777116666677777777777776aa756776bb000000001700000
00000000eeeee9aaa9eeeeeeeeeee665566eeeee00000000eee89eeeb8888565657886667777777777116666677777666666667aa756776bb000000070700000
00100100eeee9aaaaa9eeeeeeeeee556655eeeee00000000eeeeeeeeb888856599766666777777777711666667666677777777788756666bb000000017100000
00000000eeee99aaa99eeeeeeeeee556655eeeee00000000eeeeeeeebb88856599777777777777777777777777777777777777788756566bb000000001000000
00000000eeeee40404eeeeeeeeeee665566eeeee00000000eeeeeeeebbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000000000000
00000000eeeeeefffeeeeeeeeeeee665566eeeeeeee2eeeeeeeeeeeebbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb000000000000000
00000000eeeee88888eeeeeeeeeee556655eeeeeee282eeeeeeeeeeebbbbbbbb7777777777777777777777777bbbbbbbbbbbbbbbbbbbbbbbb000000000000000
00000000eeeef8fff8feeeeeeeeee556655eeeeee27872eeeeeee8eebbbbbbb777777666666676666666666667bbbbbbbbbbbbbbbbbbbbbbb000000000000000
00011000eeeef28f82feeeeeeeeee665566eeeeee28782eeeee9eeeebbbbbb777887666666667666666666666676bbbbbbbbbbbbbbbbbbbbb000000000000000
00011000eeeee28882eeeeeeeeee16655661eeee2688862eeeeeeeeebbbbb7778aa86666666676677777666666676bbbbbbbbbbbbbbbbbbbb000000000000000
00000000eeeee88888eeeeeeeeee15566551eeee2877782eeeee7eeebbbb77778aa866666666766766666666666676bbbbbbbbbbbbbbbbbbb000000000000000
00000000eeee1182811eeeeeeeee15566551eeee1288821eeeeeeeeebbb777777887666666667667777766666666676bbbbbbbbbbbbbbbbbb000000000000000
00000000eeeee11111eeeeeeeeee11111111eeeee11111eeeeeeeeeebb77777777776666666676666666666666666776bbbbbbbbbbbbbbbbb000000000000000
eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee4eeeeeeb77777777777777777777777777777777777777777777777777bbbbbb000000000000000
ee9994eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee777888888888888888777777777777777777888888888888888777bbb000000000000000
e999994eee99eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee33eeee778888111111111111177775575555555577711111111111888877777000000000000000
e999994eee94eeeeeeeeee777eeeeeeeeeeeeeeeeeeeeeeee3bb3ee4558881111aaaaaaaaaaa77755575755757777aaaaaaaa111188887888000000000000000
e499944eeeeeeeeeeeeee49994eeeeeeeeeeee888eeeeeeee33b3eee86688111aaaccccc6656677575757575557777ccccccaa111188878a8000000000000000
e444444eeeeee4eeeeeeef111feeeeeeeeeee82228eeeeeeee33ee4e86660055500ccccc66566777777777777777777cccccca00555007787000000000000000
ee4444eeeeeeeeeeeeeee15051eeeeeeeeeee48884eeeeeeeeeeeeee556055555550ccccc66566777777777777777777ccccc055555550777000000000000000
eeeeeeeeeeeeeeeeeeeeef070feeeeeeeeeeef040feeeeeeeeeeeeee6605555555550cccc66566777878777787877777cccc0555555555055000000000000000
eeeeeeeeeeeeeeeeeeeeef505feeeeeeeeeeeefffeeeeeee000000006655555755555cccccccccc778888888878777777ccc5555575555566000000000000000
ee9994eeee994eeeeeeee20000eeeeeeeeeee28882eeeeee000000006655556665555cccccccccc777777777777777777ccc5555666555566000000000000000
e999994ee99994eeeeeee24442eeeeeeeeeeff282ffeeeee000000006655576667555ccccccccccc777777777777777777cc5557666755565000000000000000
e999444ee49944eeeeeeee252eeeeeeeeeeeff161ffeeeee00000000b655556665555ccccccccccc111111111111111111cc5555666555566000000000000000
e4944eeeee444eeeeeeeee888eeeeeeeeeeeeeccceeeeeee00000000bb55555755555cccccccccccc111111111111111111c5555575555566000000000000000
e444eeeeeeeeeeeeeeeeee8e8eeeeeeeeeeeeefefeeeeeee00000000bbb555555555055555555555555555555555555555550555555555bbb000000000000000
ee44ee94eeeee4eeeeee1151511eeeeeeeee1151511eeeee00000000bbbb5555555bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb5555555bbbb000000000000000
eeeeee44eeeeeeeeeeeee11111eeeeeeeeeee11111eeeeee00000000bbbbb55555bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb55555bbbbb000000000000000
eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee8eeeeeeeee8eeeeeeeeeeee228eeeee222eeeeee822eeeee682eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee686eeee6e888eee286eeeee28786eee28882eeee67882ee688782ee8e6eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee878eee288776ee287886eee8878eeee87778eeee88782e8878782eee88868eeeeeeeeeeeeeeeeeeeeeeeeaaaeeeeee
eeeeeeeeeeeeeeeeeeeeee999eeeeeeee68886ee28788eee2878788e2278786ee68886eee678872ee688782ee687872eeeeeeeeeebbeeeeeeeeeeeaeeeaeeeee
eeeeeeeeeeeeeeeeeeeee49994eeeeeee87778ee28876eee287886eee86888eeee878eeee88868eeeee682eeeee87882eeeeeeee3bbbeeeeeeeeeeeaaaeeeeee
eeeeeeeeeeeeeeeeeeeee44444eeeeeee28882eee282eeeee286eeeeeeee6e8eee686eeeee6eeeeeeeeeeeeeee68782eeeeeebb533bbbeeeeeeeeeeeeeeeeeee
eeeeeeeebbeeeeeeeeeee40404eeeeeeee222eeeeeeeeeeeeeeeeeeeeeeeeeeeeee8eeeeeeeeeeeeeeeeeeeeeeee22eeeeee3b9b53b93eeeeeeeeee777eeeeee
eeeeeebbbb3eeeeeeeeeee444eeeeeee0000000000000000000000000000000000000000000000000000000000000000eeee33bbb333eeeeeeeeee77777eeeee
eeeeebb38bb3eeeeeeeee12221eeeeee0000700000000000000070000000000000070000000007000077700000700000eeeee333335eeeeeeeeeee76667eeeee
eeeebbbbbb333eeeeeee4412144eeeee0777770000777700000777000077770000777770007077700077700007770700eeeeee33e5eeeeeeeeeeee65656eeeee
eee3b8bbb3233eeeeeee4436344eeeee0777777000077700007777700077700007777770007777100077700001777700eeeeeee4e4eeeeeeeeee776666677eee
eee33bb33335eeeeeeeeeebbbeeeeeee0777771000777700001777100077770001777770007771000777770000177700eeeeeeee4eeeeeeeeeeee6666666eeee
eeee333355511eeeeeeeeebebeeeeeee0111710007771700000777000071777000171110007777000177710000777700eeeee11141111eeeeeeeee66666eeeee
eee115551111eeeeeeee11c1c11eeeee0000100001710100000777000010171000010000001111000017100000111100eeeeee11111eeeeeeeeeee66666eeeee
eeee1111eeeeeeeeeeeee11111eeeeee0000000000100000000111000000010000000000000000000001000000000000eeeeeeeeeeeeeeeeeeeeee6e6e6eeeee
206040207021f141100156f67456d874b9f674b9d87456f69956d899b9f699b9d89956f6fb5698fbb9f6fbb998fbb6b9e559b9e5b6b97859b978d04010206050
4083f28302f502f5f25607e740304020104083712471240083000874e7406080c0a040950095716671660008cab840307080404083f2f5f2f5028302b907e740
90a0c0b040170066006671177108fbc7405060a09040f5f2f502172217f256cad7408070b0c040f502f5f217f21722b9cad7401090b0304035b206b206d235d2
0838f640d0e001f04094009471157115000837b940d02040e040940024002471947108354940e04080014034918302f5028591891749408060f0014095719500
1500157108094940d0f060204034918591f5028302861749d0060808080806080a380a080808080a0608080a0808080608080a0808b9f6e9c80808994926c808
b040207021f14110d0d0a1321080b9f684b9f6fb56f6fb56f684b6b9b459b9b4b6b94b59b94b6040405070300086285840208060100089285840307080200008
ab584040302010000838f64050608070000808b9401060504000089458600648080a48080878f9080608080a08082806ff00ff00ff00ff00ff00ff00ff00ff00
ff00ae0080a890843f0080c890841a0080a89084eb0080789011a821159084f90080c89084cb0080789011c8212890e900809011a82115989084aa0080989011
39212890e9002890c821159890848a00809890114921159084d9002890592115789084a900807890111921a06890a45821159084b90080901169211578908489
00807890111921a08890a458212890a9008090115821a06890a41921159890846800809890111921a078901068001490a448212890a90028905821a08890a419
21159890844800809890111921a07890108800289048212890a90028904821a090106800147890a4192115a890111921a0789010f80028904821289099008090
113821a028908800147890a41921158890111921a078901009001490a43821289089008090113821a03890f800149890a4a921a098901089001490a428212890
790080289048213890100900149890a48921a0989010a90028902821289069008038904821289010a900147890a4a821a07890103a0028902821289069003890
113821a09010c900147890a48821a07890104a0028902821289069002890113821a090104a0014a89010ba002890282128905900809011482128906a00148890
10ca00289028212890490080901158212890cd00289028212890490028905821a09010bd0080901128212890490028904821a09010bd00809011382128904900
289048212890bd00809011482128904900289048212890ad008090115821289049002890482128909d008028905821a0289049002890482128908d0080389048
21a0389049002890a438211590847d00389011482138901049003890a438211590846d002890115821289010590014389048211590844d008090115821a09010
790014289058211590842d008090115821a0901099001490a4582128902d0028905821a09010b9001490a4482128902d0028904821a09010d900289048211590
841d00289048212890e900289058211590840d00289048212890e9001490a45821289084fc00289048212890f9001490a44821389084ec002890482128900a00
1490a4382115389084cc008090113821a090101a001490a43821155890848c008090113821a090103a0028904821155890847c002890482128904a0028909821
157890840c002890482128904a001490a4982115789084fb002890482128905a001490a4f821157890848b002890482128906a001490a4f821157890847b0028
90482128907a00147890a4f821153890844b002890482128908a00147890a4f821153890843b00289048212890fa00147890a49821153890842b002890482128
900b00147890a49821153890841b00289048212890846b00145890a478211590840b00289048213890846b00145890a47821159084fa001490a43821153890bb
00143890a4582115389084da001490a43821152890cb00143890a4582115389084da00289048212890db00143890a4582115389084ca00289048212890eb0014
3890a4582115389084ba002890a438211590840c001490a47821159084aa003890a43821159084fb0080289088212890aa0014389048212890cb008058908821
2890ba0014289048212890bb008058901188212890ca00289048211590845b0080589011d8212890ca00289058211590843b0080589011d821a09010ca001490
a45821159084da0080589011d821a0589010ea001490a45821159084ba0080589011d821a05890100b001490a458212890845a0080589011d821a05890106b00
1490a448213890843a0080589011d821a05890108b002890a438211538902a00809011d821a0589010db003890a438211528901a00809011d821a0589010eb00
1438904821159084d900803890119821a05890104c001428905821159084b900803890119821a05890106c001490a458212890a900803890115821a0589010cc
001490a4482128909900803890115821a0589010ec002890482128908900803890115821a090103d002890482128907900803890115821a090104d0028904821
289069008090115821a0389010ba0080c99084c80028904821289059008090115821a0389010ba0080e99084b80028904821289049008090115821a0389010ba
00809011c921159084a800289048212890490028905821a0389010ca002890e9211590849800289048212890490028904821a0389010da0028904821a08890a4
19211590848800289048212890490028904821389010ea0028904821a890a4192128908800289048212890490028904821289010fa0028904821289010680014
d890a448212890880028904821289049002890482128900b00289048212890880014d89048212890880028904821289049002890482128900b00289048212890
390014289048212890880028904821289049002890482128900b002890482128904900289048212890880028904821289049002890482128900b002890482128
904900289048212890880028904821289049002890482128900b002890482128904900289048212890880028904821289049002890482128900b002890482128
904900289048212890880028904821289049001490a43821159084fa002890482128904900289048212890880028904821289059001490a43821159084ea0028
9048212890490028904821289088002890482128906900289048212890da008090113821a09010490028904821289088002890482128906900289048212890ca
008090113821a09010590028904821289088002890482128906900289048212890ca002890482128906900289048212890880028904821289069002890482128
90ca0028904821289069002890482128908800289048212890690028904821289084ba0028904821289069001490a43821159084780028904821289069002890
4821389084aa0028904821289079001490a438211590846800289048212890690028904821153890849a00289048212890890028904821289068002890482128
90690028907821153890846a002890482128908900289048212890680028904821289069001490a47821153890845a0028904821289089002890482128906800
28904821289079001490a49821153890842a002890482128908900289048212890680028904821289089001490a49821153890841a0028904821289089002890
4821289068002890482128909900143890a4982115389084e90028904821289089002890482128906800289048212890a900143890a4982115389084c9008090
113821a0901089002890482128906800289048212890d900143890a498211538908489008090113821a0901099002890482128906800289048212890e9001438
90a4982115389084690080289048212890a90028904821289068002890482128901a00143890a4982115a99048212890a9002890482128906800289048212890
2a00143890a498211589901148212890a900289048212890844800802890482128905a00143890a44a212890a90028904821a890482128906a00143890a43a21
2890a9002890482115889011482128909a00143890a40a212890a900289029212890aa00143890a4e921a09010a9001490a40921a09010da00140a9010c90014
299010fa0014e99010e90014099010ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00890000742877042022380052554378773702280073687757004066
46580010287757887714280063557666763877370022025800302877577578774728002111322844662877478800302877372153487757557704480020114375
77778800107677272800487713117337680031647777980075774700107528774510116247015800206477778800207577250020565567124364287701580030
64777788002810750300201331765877065800307577770198003003380031755877575800202877670298001001380031787702580028777702980010480031
787705580071777704e8003076587767245800407777166800201568001273587767246800747727680060773543480001207428776777671468006377266800
60287767680021487766026800637715680050287757680020387747137800634702780028770758001151387714780030751488005055680034537756550340
4438004404407767090010004201110028770702702877517777c800303378004028776746742877547777c80076770668004028775723762877547767b80030
287737680040287747413877547747b800302877377800287707623877107747a80020762877372800202223132028772662287706107507a800207628772700
103866272028772662776702107527a8002076387702203877172028772640664628007517b800743877672048770028770400220228007503b8002048771675
3877077447224800105501c80072387767764877727766143800105501c80040987772287736280010315711d8007288774628772600205475775302c8002088
7727287726280076287737d80060887707766604280072287717c8002076287755754877276223380074287715c80076287737113048772720480072287705b8
006028775513280074387726580062287705b80072773711380040387704580040667715b8007277174800207628777800227415b80072775748002038770278
00723501a800722877024800767767027800727745a8003877044800722877027800767767980040387706480072287702680020767707980076387704480062
77670268002076774758004426445877024800627757280022480020767747480070787767580040771301006215102146007628770010731375787707580020
350128006277557567027228775755775778776778000138004066287767246458773775687702c80022642877677658771570587707a8000138004066387758
7715004426447747090022642877587715790062287758770779004028775877058900747748773799004077487705a90072487715a90040487715a900724877
__label__
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000001111111110011111111111100000011111000000111111100111111111100000000000000000000000000000000000000000000000000000000
0000000000001ccccccccc11ccccc11ccccc100011ccccc100011ccccccc11cccccccccc10000000000000000000000000000000000000000000000000000000
00000000000111111111111111111111111110011111111110111111111111111111111110000000000000000000000000000000000000000000000000000000
00000000001ccccccccccc11ccccc11ccccc101cccccccccc11cccc11ccc11cccccccccc10000000000000000000000000000000000000000000000000000000
00000000011111111111111011111111111101111111111111111111111101111111111110000000000000000000000000000000000000000000000000000000
0000000001ccccc1111111001cccccccccc101ccccc11ccccc1ccccccc1101cc1cccc1cc10000000000000000000000000000000000000000000000000000000
00000000011111111111111011111111111101111111111111111111111100111111111100000000000000000000000000000000000000000000000000000000
0000000001ccccc11ccccc101cccc11cccc101ccccc11ccccc1111cccccc10111cccc11100000000000000000000000000000000000000000000000000000000
00000000011111111111111011111111111101111111111111111111111110001111110000000000000000000000000000000000000000000000000000000000
00000000001c7ccc11ccc101ccccc11cc7c7101ccccc777cc117cc11cccc1001ccc77c1000000000000000000000000000000000000000000000000000000000
00000000001111111111110111111111111110111111111111111111111100011111111000000000000000000000000000000000000000000000000000000000
0000000000011c7cccc11001cc7cc11cc7cc100111c7ccc1101cc7cc7c110001c7cccc1000000000000000000000000000000000000000000000000000000000
00000000000111111111100011111111111100001111111100011111111000001111110000000000000000000000000000000000000000000000000000000000
00000000000001111110000011111111111100000011111000077777777770001177777777000777777000007777770000077777077770000000000000000000
00000000000000000000000000000000000000000000000000077777777777000077777777000777777000007777770000077777077770000000000000000000
00000000000000000000000000000000000000000000000000177777777777700177777777101777777100017777771000177777177771000000000000000000
00000000000000000000000000000000000000000000000000167777666777700167767776101677776100016777761000167777177761000000000000000000
00000000000000000000000000000000000000000000000000117777111777710177717777101177771100011777711000116777177611000000000000000000
00000000000000000000000000000000000000000000000000017777777777610077717777000177771000001777710000011777777110000000000000000000
00000000000000000000000000000000000000000000000000017777777777110177777777100177771000001777710000001677776100000000000000000000
00000000000000000000000000000000000000000000000000017777667777100777666777700177771077701777710777001177771100000000000000000000
00000000000000000000000000000000000000000000000000077777117777777777117777770777771077707777710777000777777000000000000000000000
00000000000000000000000000000000000000000000000000077777716777777777107777770777777777717777777777100777777000000000000000000000
00000000000000000000000000000000000000000000000000177777711677777777117777771777777777717777777777101777777100000000000000000000
44444444444424242424242424242424444444444bbbbbbbbb1666666111666666661166666616666666666166666666661b166666613bbbbbbbbbbbbbbbbbbb
4444444444424242424242424242424444444444444444bbbb11111111b1111111111111111111111111111111111111111311111111b3bbbbbbbbbbbbbbbbbb
444444444424242424242424242424444444444444444444443b3b3b3b3b3b3b3b3b3b3bbbbbbbbbbbbbbbbbbbbb3b3b3b3b3b3b3b3b3b3bbbbbbbbbbbbbbbbb
444444444542424242424242424244444444444444444444444243b3b3b3b3b3b3b3b3bbbbbbbbbbbbbbbbbbbbbbb3b3b3b3b3b3b3b3b3b3bbbbbbbbbbbbbbbb
4444444454545424242424242424444444444444444444444424242b3b3b3b3b3b3b3b3bbbbbbbbbbbbbbbbbbbbb3b3b3b3b3b3b3b3b3b3b3bbbbbbbbbbbbbbb
4444444545454542424242424242444444444444444444444242424242b3b3b3b3b3b3bbbbbbbbbbbbbbbbbbbbbbb3b3b3b3b3b3b3b3b3b3b3bbbbbbbbbbbbbb
54545555555555552222222222242424242424242424242422222222222233333333333b3b3b3b3b3b3b3b3b3b3b3b33333333333333333333333b3b3b3b3b3b
454555555555555552222222224242424242424242424242422222222222222333333333b3b3b3b3b3b3b3b3b3b3b3333333333333333333333333b3b3b3b3b3
5455555555555555555222222424242424242424242424242222222222222222233333333b3b3b3b3b3b3b3b3b3b3b3333333333333333333333333b3b3b3b3b
455555555555555555599222224242424242424242424242222222222222222222233333b3b3b3b3b3b3b3b3b3b3b3b3333333333333333333333333b3b3b3b3
5555555555555555555945222424242424242424242424242222222222222222222222333b3b3b3b3b3b3b3b3b3b3b3b3333333333333333333333333b3b3b3b
555555555555555555555552424242424242424242424242222222222222222222222222b3b3b3b3b3b3b3b3b3b3b3b3b3333333333333333333333332424242
555555555555555555555544542424242424242424242422222222222222222222222222242b3b3b3b3b3b3b3b3b3b3b33333333333333333333333322242424
555555555555555555555544454242424242424242424242222222222222222222222222424243b3b3b3b3b3b3b3b3b3b3333333333333333333333222224242
5555555555555555555554545454242424242424242424222222222222222222222222222424242b3b3b3b3b3b3b3b3b3b333333333333333333332222222424
5555555555555555555545454545424242424242424242222222222222222222222222222242424242b3b3b3b3b3b3b3b3b33333333333333333222222222242
5555555555555555555454545454545424242424242424222222222222222222222222222424242424243b3b3b3b3b3b3b3b3333333333333332222222222224
454545454545454545444444444444444444444444444442424242424242424242424242444444444444444bbbbbbbbbbbbbb3b3b3b3b3b3b342424242424242
54545454545454545444444444444444444444444444442424242424242424242424242424444444444444444bbbbbbbbbbbbb3b3b3b3b3b3424242424242424
45454545454545454444444444444444449999944444424242424242424242424242424242444444444444444444bbbbbbbbbbb3b3b3b3b34242424242424242
54545454545454544444444444444444499999994444442424242424242424242424242424444444444444444444444bbbbbbbbb3b3b3b242424242424242424
4545454545454544444444444444444449999999444442424242424242424242424242424244444444444444444444444bbbbbb3b3b3b2424242424242424242
5454545454545444444444444444444449999444444424242424242424242424242424242444444444444444444444444444bbbb3b3b24242424242424242424
4545454545454444444444444444444444994444444442424242424242424242424242424244444444444444444444444444444bb3b242424242424242424242
54545454545454444444444444444444449944444999994424242424242424242424242424444444444444444444444444444444442424242424242424242424
45454545454544444444444444444444444444449999999942424277774242424242424242444444444444444444444444444444444242424242424242424242
54545454545444444444444444444444444444449999999944447777777724242424242424244444444444444444444444444444444424242424242424242424
45454545454444444444444444444444444444449999999947777777777772424242424242444444444444444444444444444444444242424242424242424242
54545454544444444444444444444444444444449999987777777777777777742424242424244444444444444444444444444444444424242424242424242424
45454545444444444444444444444444444444444997777777777777777777774242424242444444444444444444444444444444444442424242424242424242
54545454444444444444444444444444444444444447777777777777777777777424242424244444444444444444444444444444444444242424242424242424
454545444444444444444444444444444444444447777a7667777777777777777742424242424444444444444444444444444444444444424242424242424242
545454544444444444444444444444444444444445877a8667777777777777711174242424244444444444444444444444444444444444242424242424242424
45454544444444444444444444444444444444444888786666677777777711111672424242424444444444444444444444444444444444424242424242424242
55555454545454545454545454545454545454545661876666677777771111166667222222222424242424242424242424242424242424242222222222222222
55554545454545454545454545454545454545455601a87667667777111116666666722222224242424242424242424242424242424242422222222222222222
55545454545454545454545454545454545454545655a17767666711111666666666722222222424242424242424242424242424242424242222222222222222
555545454545454545454545454545454545454555555c1776766711166666666666672222222242424242424242424242424242424242424222222222222225
555454545454545454545454545454545454545555565cc177666716666666666667777222222424242424242424242424242424242424242422222222222255
5545454545454545454545454545454545454545555575c577766766666666666557776722222242424242424242424242424242424242424242222222222255
5454545454545454545454545454545454545455511575cc67766766666666655577777672222424242424242424242424242424242424242422222222222555
4545454545454545454545454545454545454555551155c675576776666665557777777777222242424242424242424242424242424242424242222222225555
5454545454545454545454545454545454545455555115ccc7557676666555777777778767722424242424242424242424242424242424242424222222225555
4545454545454545454545454545454545454555555511ccc7757776675577777777881176772242424242424242424242424242424242424242422222255555
54545454545454545454545454545454545455555555111cc77778777777777777781aac77677224242424242424242424242424242424242424242222555555
454545454545454545454545454545454545455555555111c787778767777778777811ac76767742424242424242424242424242424242424242424225555555
5454545454545454545454545454545454545555555555111c78771867777788877811cc76767724242424242424242424242424242424242424242225555555
454545454545454545454545454545454545455555555551111787c186777887887781ac76777745454545454545454545454545454545454545454555555555
545454545454545454545454545454545454555555555555111178cc17667888877788177766a854545454545454545454545454545454545454545455555555
4545454545454545454545454545454545455555555555551111777cc1767887777787777665aa75454545454545454545454545454545454545454545555555
5454545454545454545454545454545454545555555555555111177cc187677777777776655aa754545454545454545454545454545454545454545454555555
4545454545454545454545454545454545455555555555555511117cca1876767777775556675665454545454545454545454545454545454545454545455555
54545454545454545454545454545454545555555555555555511117c05877677677666567556654545454545454545454545454545454545454545454555555
45454545454545454545454545454545454555555555555555551151c55887677666557775677655454545454545454545454545454545454545454545455555
54545454545454545454545454545454545555555555555555551115c55588767655677566576654545454545454545454545454545454545454545454545555
45454545454545454545454545454545455555555555555555555115c5650877a567756566666155454545454545454545454545454545454545454545454555
5454545454545454545454545454545454555555555555555555551115765788aa75566656611115545454545454545454545454545454545454545454545455
45454545454545454545454545454545455555555555555555555551115655887756655661111555454545454545454545454545454545454545454545454545
24545454545454545454545454545454555555555555555555555551115575775665656111115555545454545454545454545454545454545454545454545455
42454545454545454545454545454545455555555555555555555555115556556755611111555555454545454545454545454545454545454545454545454545
24545454545454545454545454545454555555555555555555555555511555667766111115555555545454545454545454545454545454545454545454545454
42454545454545454545454545454545555555555555555555555555551155567611111555555555554545454545454545454545454545454545454545454545
24245454545454545454545454545454555555555555555555555555555111666111115555555555545454545454545454545454545454545454545454545454
42424545454545454545454545454545555555555555555555555555555111611111555555555555554545454545454545454545454545454545454545454545
24242454545454545454545454545455555555555555555555555555555511111115555555555555545454545454545454545454545454545454545454545454
44444444444444444444444444444445454545454545454545454545454541111545454545454545444444444444444444444444444444444444444444444444
44444444444444444444444444444454545454545454545454545454545454145454545454545454544444444444444444444444444444444444444444444444
44444444444444444444444444444445454545454545454545454545454545454545454545454545454444444444444444444444444444444444444444444444
44444444444444444444444444444454545454545454545454545454545454545454545454545454544444444444444444444444444444444444444444444444
11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
44444444444444444444444444444454545454545454545454545454545454545454545454545454544444444444444444444444444444444444444444444444
11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
44444444444444444444444444444454545454545454777477747774545457747774777454547754745447744444444444444444444444444444444444444444
11111111111111111111111111111111111111111110117071707110111171101710171011101700701171101111111111111111111111111111111111111111
44444444444444444444444444445454545454545450777070707770545070000700070054500700777077704444444444444444444444444444444444444444
11111111111111111111111111111111111111111110711070701170111070710701070111110700717011701111111111111111111111111111111111111111
44444444444444444444444444445454545454545450777077707770545077700704777454547770777077104444444444444444444444444444444444444444
11111111111111111111111111111111111111111110111011101110111011100100111011101110111011001111111111111111111111111111111111111111
44444444444444444444444444445454545454545450000000000000545000000000000054500000000000044444444444444444444444444444444444444444
11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
44444444444444444444444444545454545454545454545454545454545454545454545454545454545444444444444444444444444444444444444444444444
11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
44444444444444444444444444545454545454545454545454545454545454545454545454545454545444444444444444444444444444444444444444444444
11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
44444444444444444444444444546664665464645454646466646464545454545664666466646664666454444664666466646664444444444444444444444444
11111111111111111111111111106160616060601110606061106060161111116110161061606160161011116110616066606110111111111111111111111111
44444444444444444444444454506660606066605450661066006660010454506660060066606610060054406000666061606600444444444444444444444444
11111111111111111111111111106160606011601110616061001160060111101160060061606160060111106060616060606101111111111111111111111111
44444444444444444444444454506060606066605450606066606660010454506610060060606060060454406660606060606664444444444444444444444444
11111111111111111111111111101010101011101110101011101110000111101100010010101010010111101110101010101110111111111111111111111111
44444444444444444444444454500000000000005450000000000000545454500004000000000000000454400000000000000000444444444444444444444444
11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111
44444444444444444444445454545454545454545454545454545454545454545454545454545454545454444444444444444444444444444444444444444444
11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111

__map__
739a004785773099004785775199002785777311109700048677555285001232109000468677628400025777631088003341113431820024837774677640820001111483776410244311830006827757827763101709071d0b3506370a370f3413321a3521392638393239302a29292329203814390833062a0c251b20141b09
180410720a05010a0901300602320502350502370602380802380f02380b023711023a38023a3a02393b02363b02303702313902323b02242802222802212902212a022e2802302802312a02312c021e3b02213b02233802223902181c021b1e021c1f021d21021c22021a23021421020706030b05030b0b030f0b030f060324
0803260803280803270b03270c032a0c032a0b032b0a032b07030a37030531030b3403103a030633030d3803082e031036030931030f39030c04040d06040e07040c0a040e0c04070704050804070904090b040a0c04080c04040b04050b041808041809041f0d041b0d04190c043524043b2604332304392204372004392404
062604141e04161f04252c041e36041d37040c2804112704152004132504112104262c040634040a14030814030616030517030619030919030a19030a1a03071b030a1c030c19030e16030c15030d1b030b16030a11030314030000000000000000000000000000000000000000000000000000000000000000000000000000
__sfx__
000100031b340146400e7700c070100700c070100700c070100700c070100700c070100700c070100700c070100700d070100700c070100700c070100700c070100700c070100700c070100700c070100700c070
000900001e7501e7001d7001d7001c7001b7001a70018700167001570013700117000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000400002575025750257402573025730257202571025710127001d7001d700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000200040e3500e6500e3500e6500c350076500435001650013500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
001000003f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503e05038050350502c050250501e0501805016050150501305013050120501205011050110501105011050
001000003f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503f0503e0503b05039050380503605034050310502c05027050220501e0501c0501805014050
000100000a6500e6500f1500d15009150051500215000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00030000273301d3302a33000000003002a32027300000002a3202930006300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00020000182501c65025250226301e230162200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000300002d6501c640156400d63000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000400002a620246101f610086000710009600086001d600056000460002600016000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000200000f770097600d6500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

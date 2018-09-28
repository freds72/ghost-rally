pico-8 cartridge // http://www.pico-8.com
version 16
__lua__
-- globals
local time_t,time_dt=0,1/30
local actors,ground_actors,parts,v_light,cam,plyr,active_ground_actors={},{},{},{0,1,0}
local physic_actors={}
-- physic thresoholds
local k_small=0.001
local k_small_v=0.01
local k_depth=0.05
-- baumgarte
local k_bias=0.2
local k_slop=0.05

local k_coll_none,k_coll_pen,k_coll_coll,k_coll_rest=0,1,2,4

-- world units
local ground_shift,hscale=1,4
local ground_scale=2^ground_shift
local v_grav={0,-1,0}
local world={}

local good_side,bad_side,any_side,no_side=0x1,0x2,0x0,0x3

-- register json context here
local _tok={
 ['true']=true,
 ['false']=false}
function nop() return true end
local _g={
	good_side=good_side,
	bad_side=bad_side,
	any_side=any_side,
	nop=nop}

-- json parser
-- from: https://gist.github.com/tylerneylon/59f4bcf316be525b30ab
local table_delims={['{']="}",['[']="]"}
local function match(s,tokens)
	for i=1,#tokens do
		if(s==sub(tokens,i,i)) return true
	end
	return false
end
local function skip_delim(str, pos, delim, err_if_missing)
 if sub(str,pos,pos)!=delim then
  if(err_if_missing) assert'delimiter missing'
  return pos,false
 end
 return pos+1,true
end
local function parse_str_val(str, pos, val)
	val=val or ''
	if pos>#str then
		assert'end of input found while parsing string.'
	end
	local c=sub(str,pos,pos)
	if(c=='"') return _g[val] or val,pos+1
	return parse_str_val(str,pos+1,val..c)
end
local function parse_num_val(str,pos,val)
	val=val or ''
	if pos>#str then
		assert'end of input found while parsing string.'
	end
	local c=sub(str,pos,pos)
	-- support base 10, 16 and 2 numbers
	if(not match(c,"-xb0123456789abcdef.")) return tonum(val),pos
	return parse_num_val(str,pos+1,val..c)
end
-- public values and functions.

function json_parse(str, pos, end_delim)
	pos=pos or 1
	if(pos>#str) assert'reached unexpected end of input.'
	local first=sub(str,pos,pos)
	if match(first,"{[") then
		local obj,key,delim_found={},true,true
		pos+=1
		while true do
			key,pos=json_parse(str, pos, table_delims[first])
			if(key==nil) return obj,pos
			if not delim_found then assert'comma missing between table items.' end
			if first=="{" then
				pos=skip_delim(str,pos,':',true)  -- true -> error if missing.
				obj[key],pos=json_parse(str,pos)
			else
				add(obj,key)
			end
			pos,delim_found=skip_delim(str, pos, ',')
	end
	elseif first=='"' then
		-- parse a string (or a reference to a global object)
		return parse_str_val(str,pos+1)
	elseif match(first,"-0123456789") then
		-- parse a number.
		return parse_num_val(str, pos)
	elseif first==end_delim then  -- end of an object or array.
		return nil,pos+1
	else  -- parse true, false
		for lit_str,lit_val in pairs(_tok) do
			local lit_end=pos+#lit_str-1
			if sub(str,pos,lit_end)==lit_str then return lit_val,lit_end+1 end
		end
		assert'invalid json token'
	end
end

-- screen space effects
local shkx,shky=0,0
function screen_shake(pow)
	shkx,shky=min(4,shkx+rnd(pow)),min(4,shky+rnd(pow))
end
function screen_update()
	shkx*=-0.7-rnd(0.2)
	shky*=-0.7-rnd(0.2)
	if abs(shkx)<0.5 and abs(shky)<0.5 then
		shkx,shky=0,0
	end
	camera(shkx,shky)
end

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
function v_print(v,x,y,c)
	print(v[1].."|"..v[2].."|"..v[3],x,y,c)
end
function sqr_dist(a,b)
	local dx,dy,dz=b[1]-a[1],b[2]-a[2],b[3]-a[3]

	dx=dx*dx+dy*dy+dz*dz
	return dx<0 and 32000 or dx
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
function v_lerp(a,b,t)
	return {
		lerp(a[1],b[1],t),
		lerp(a[2],b[2],t),
		lerp(a[3],b[3],t)}
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
function v_clamp(v,l)
	local d=v_dot(v,v)
	if d>l*l then
		v_scale(v,l/sqrt(d))
	end
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
function m_inv_x_v(m,v,p)
	local x,y,z=v[1],v[2],v[3]
	v[1],v[2],v[3]=m[1]*x+m[2]*y+m[3]*z,m[4]*x+m[5]*y+m[6]*z,m[7]*x+m[8]*y+m[9]*z
end

-- generic matrix inverse
function m_inv(me)
	local te={
	me[9]*me[5]-me[6]*me[8],
	me[9]*me[2]+me[3]*me[8],
	me[6]*me[2]-me[3]*me[5],
	-me[9]*me[4]+me[6]*me[7],
	me[9]*me[1]-me[3]*me[7],
	-me[6]*me[1]+me[3]*me[4],
	me[9]*me[4]-me[5]*me[8],
	-me[8]*me[1]+me[2]*me[7],
	me[5]*me[1]-me[2]*me[4]}

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

		-- angular velocity "converted" to quaternion
		-- not: q[v,0]!!
		--[[
	local qdot=v_clone(v)
	qdot[4]=0
	q_x_q(qdot,q)
	q_scale(qdot,0.5)
	q[1]+=dt*qdot[1]
	q[2]+=dt*qdot[2]
	q[3]+=dt*qdot[3]
	q[4]+=dt*qdot[4]
	q_normz(q)
	]]
end

function q_scale(q,scale)
	return {scale*q[1],scale*q[2],scale*q[3],scale*q[4]}
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

-- model bounding box
function get_modelsize(model)
	local vmin,vmax={32000,32000,32000},{-32000,-32000,-32000}
	for _,v in pairs(model.v) do
		vmin,vmax=v_min(vmin,v),v_max(vmax,v)
	end
 return make_v(vmin,vmax)
end

-- models & rendering
local all_models=json_parse'{"audi":{}}'
local dither_pat=json_parse'[0b1111111111111111,0b0111111111111111,0b0111111111011111,0b0101111111011111,0b0101111101011111,0b0101101101011111,0b0101101101011110,0b0101101001011110,0b0101101001011010,0b0001101001011010,0b0001101001001010,0b0000101001001010,0b0000101000001010,0b0000001000001010,0b0000001000001000,0b0000000000000000]'
local dither_pat2=json_parse'[0xffff,0xa5a5,0x0000]'

function draw_model(model,m,pos)

	-- cam pos in object space
	local cam_pos=v_clone(cam.pos)
	v_add(cam_pos,pos,-1)
	m_inv_x_v(m,cam_pos)
	-- v_light dir in object space
	local l=v_clone(v_light)
	m_inv_x_v(m,l)
	
	-- faces
	local faces,p={},{}
	for i=1,#model.f do
		local f,n=model.f[i],model.n[i]
		-- viz calculation
		local d=v_dot(n,cam_pos)
		f.flipn=(f.double_sided and d<model.cp[i]) and -1 or 1
		
		if f.double_sided or d>=model.cp[i] then
			-- project vertices
			for _,vi in pairs(f.vi) do
				if not p[vi] then
					local v=model.v[vi]
					local x,y,z=v[1],v[2],v[3]
					x,y,z,w=cam:project(m[1]*x+m[4]*y+m[7]*z+pos[1],m[2]*x+m[5]*y+m[8]*z+pos[2],m[3]*x+m[6]*y+m[9]*z+pos[3])
					p[vi]={x,y,z,w}
				end
			end
			-- distance to camera (in object space)
			local d=sqr_dist(f.center,cam_pos)

			-- register faces
			add(faces,{key=d,face=f})
		end
	end
	-- sort faces
	sort(faces)

	-- draw faces using projected points
	for _,f in pairs(faces) do
		f=f.face
		local c=max(f.flipn*v_dot(model.n[f.ni],l))*5
		c=sget(c+8,f.c)
		local p0=p[f.vi[1]]
	 	for i=2,#f.vi-1 do
		 	local p1,p2=p[f.vi[i]],p[f.vi[i+1]]
		 	trifill(p0[1],p0[2],p1[1],p1[2],p2[1],p2[2],c)
		end
	end
end

function draw_model_shadow(model,m,pos)
	-- v_light dir in object space
	local l=v_clone(v_light)
	m_inv_x_v(m,l)
	
	-- faces
	local p={}
	for i=1,#model.f do
		local f,n=model.f[i],model.n[i]
		-- viz calculation
		if f.double_sided or v_dot(n,l)<0 then
			-- project vertices
			for _,vi in pairs(f.vi) do
				if not p[vi] then
					local v=m_x_v(m,model.v[vi])
					v_add(v,pos)
					v[2]=get_altitude(v[1],v[3])
					local x,y,z,w=cam:project(v[1],v[2],v[3])
					p[vi]={x,y,z,w}
				end
			end
			-- draw faces using projected points
			-- (no need to sort)
			local p0=p[f.vi[1]]
		 	for i=2,#f.vi-1 do
			 	local p1,p2=p[f.vi[i]],p[f.vi[i+1]]
		 		trifill(p0[1],p0[2],p1[1],p1[2],p2[1],p2[2],1)
			end
		end
	end
end

function add_tireforce(self,v,offset,scale)
 -- vector to world
	v=m_x_v(self.m,v)
	
	-- todo: clamp
	--local ratio=mid(5*v_dot(force,self.v),-5,5)
	local ratio,slide=scale,false
	if not ratio then
		ratio=-v_dot(v,self.v)
		-- sliding?
		slide=abs(self.traction_ratio*ratio)>1
	end
	-- wheels on ground?
	ratio*=self.traction_ratio
	v_scale(v,ratio*self.mass_inv*30)

	-- application point (world space)
	local pos=v_clone(self.pos)
	v_add(pos,m_fwd(self.m),offset)
	self:add_force(v,pos)
	
	--if slide then
		add(pos,v_up)
		make_part("smoke",pos)
	--end
end

_g.control_plyr=function(self)
	local turn,z=0,0
	if(btn(0)) turn=1
	if(btn(1)) turn=-1

 --[[
	if(btn(2)) z=-1
	if(btn(3)) z=1
	plyr.pos[1]-=turn/4
	plyr.pos[3]+=z/4
 ]]
 
	self.turn+=turn/2
	
	if v_dot(self.v,self.v)>k_small then
		-- steering angle
		local angle=0.25+0.1*self.turn/2.33
		add_tireforce(self,{-sin(angle),0,cos(angle)},1)
		-- rear wheels
		add_tireforce(self,v_right,-1)
	end

	-- accelerate
	if btn(2) then
		add_tireforce(self,v_fwd,-1,12)
	end
	-- brake
	if btn(3) then
		add_tireforce(self,v_fwd,0,-4)
	end
	
	if btn(4) or btn(5) then
		local pos=v_clone(self.pos)
		v_add(pos,m_up(self.m),3)
		local force=v_clone(v_up)
		v_scale(force,12)
		self:add_force(force,pos)
	end
end

_g.update_plyr=function(self)
	local up=m_up(self.m)
	-- time decay
	self.traction*=0.8
	self.turn*=0.7
	
	for i=1,4 do
		local v=self.bbox.v[i]
		if v.contact_t and time_t-v.contact_t<5 then
			-- contact quality
			local r=max(v_dot(up,v.n))
			self.traction+=r
		end
	end
	self.traction_ratio=self.traction/20
	
	--make_part("smoke",pos,v_up)
	return true
end

_g.draw_plyr_shadow=function(self)
	draw_model_shadow(all_models["audi_bbox"],self.m,self.pos)
end

local all_actors=json_parse'{"plyr":{"model":"audi","hardness":0.02,"mass":16,"turn":0,"traction":0,"traction_ratio":0,"control":"control_plyr","update":"update_plyr","draw_shadow":"draw_plyr_shadow"},"tree":{"model":"tree","update":"nop","rnd":{"angle":[0,1]}}}'

function draw_actor(self)
	draw_model(self.model,self.m,self.pos)
end

function make_actor(src,p)
	-- instance
	local a=clone(all_actors[src],{
		pos=v_clone(p),
		q=q or make_q(v_up,0.25)
	})
	a.model,a.draw=all_models[a.model],a.draw or draw_actor
	-- init orientation
	a.m=m_from_q(a.q)
	return add(actors,a)
end

-- note: limited to a single actor per tile
function make_ground_actor(src,i,j)
	local x,z=shl(i+rnd(),ground_shift),shl(j+rnd(),ground_shift)
	local a=clone(all_actors[src],{
		pos={x,get_altitude(x,z),z}
	})
	a.model=all_models[a.model]
	a.draw=a.draw or draw_actor
	-- any angle defined in instance?
	local q=make_q(v_up,a.angle or 0)
	local m=m_from_q(q)
	a.m=m
	-- register
	ground_actors[i+j*128]=a
	return a
end

-- registers a ground collision
function make_ground_contact(a,p,n,d)
	local padot=a:pt_velocity(p)
	local vrel=v_dot(n,padot)
	-- resting condition?
	if(d<k_small and vrel>-k_small_v) return
			
	local c={
		-- body
		a=a,
		-- normal
		n=n,
		-- body contact point
		-- world position
		p=p,
		-- penetration
		d=d,
		-- relative velocity
		v=vrel,
		-- 
		nimpulse=0,
		pre_solve=function(self,dt)
			local a,n=self.a,self.n
			
			local ra=make_v(a.pos,self.p)
			local racn=make_v_cross(ra,n)

			local nm=a.mass_inv
			nm+=v_dot(racn,m_x_v(a.i_inv,racn))
			self.nm=1/nm
			
			-- baumgarte
			local bias=-k_bias*max(self.d+k_slop)/dt

			-- restitution bias
			local va=v_clone(a.v)
			v_add(va,make_v_cross(a.omega,ra))
			local dv=-v_dot(va,n)
			-- find out unit??
			if dv<-1 then
				bias-=a.hardness*dv
			end
			self.bias=bias
			self.ra=ra
		end,
		solve=function(self)
			local a,dv,n=self.a,v_clone(self.a.v),v_clone(self.n)
			v_add(dv,make_v_cross(a.omega,self.ra))

			local vn=v_dot(dv,n)
			local lambda=-self.nm*(vn+self.bias)
  	
			local tempn=self.nimpulse
			self.nimpulse=max(tempn+lambda)
			lambda=self.nimpulse-tempn
			
			-- impulse too small
			if(lambda<k_small) return
  	-- correct linear velocity
			v_scale(n,lambda)			
			v_add(a.v,n,a.mass_inv)
			-- correct angular velocity
			v_add(
				a.omega,
				m_x_v(
					a.i_inv,
					make_v_cross(self.ra,n)
				))
		end
	}
	return c
end

-- rigid body extension for a given actor
-- actor must have a 3d model
function make_rigidbody(a,bbox)
	local rb={
		force=v_zero(),
		torque=v_zero(),
		-- bounding box
		bbox=bbox,
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
			-- register a force
		add_force=function(self,f,p)
			v_add(self.force,f,self.mass)
			v_add(self.torque,make_v_cross(make_v(self.pos,p),f))
		end,
		-- apply forces & torque for iteration
		prepare=function(self,dt)
			-- add gravity
			v_add(self.force,{0,-9.8*self.mass,0})
		
			-- inverse inertia tensor
			self.i_inv=m_x_m(m_x_m(self.m,self.ibody_inv),m_transpose(self.m))
	
			-- velocity
			v_add(self.v,self.force,self.mass_inv*dt)
	
			-- angular velocity
			v_add(self.omega,m_x_v(self.i_inv,self.torque),dt)
			
			-- damping
			v_scale(self.v,1/(1+dt*0.4))
			v_scale(self.omega,1/(1+dt*0.8))
		end,
		integrate=function(self,dt)
			v_add(self.pos,self.v,dt)
			q_dydt(self.q,self.omega,dt)
			self.m=m_from_q(self.q)
			-- clear forces
			self.force=v_zero()
			self.torque=v_zero()
		end,
		update_contacts=function(self,contacts)
			local i=0
			for _,v in pairs(self.bbox.v) do
				-- to world space
				local p=m_x_v(self.m,v)
				v_add(p,self.pos)
				local h=get_altitude(p[1],p[3])
				local depth=h-p[2]
				if depth>k_small then
					local n=get_normal(p[1],p[3])
					depth=v_dot(n,{0,depth,0})
					-- deep enough?
					if depth>-k_small then
						local ct=make_ground_contact(self,p,n,depth)
						if ct then
							add(contacts,ct)
							-- record contact time
							v.contact_t=time_t
							v.n=n
						end
					end
				end
			end
		end
	}
	
	-- compute inertia tensor
	local size=v_sqr(get_modelsize(bbox))
	local ibody=make_m(size[2]+size[3],size[1]+size[3],size[1]+size[2])
	m_scale(ibody,a.mass/12)
	
	-- invert 
	rb.ibody_inv=m_inv(ibody)
	
	-- register rigid bodies
	return add(physic_actors,clone(rb,a))
end

-- physic world
function world:check_coll()
	self.contacts={}
	for _,a in pairs(physic_actors) do
		a:update_contacts(self.contacts)
	end
end

function world:update()
	local dt=1/30
	
	-- collect contacts
	self:check_coll()

	-- 
	for _,a in pairs(physic_actors) do
		a:prepare(dt)
	end
	-- solve contacts
	for _,c in pairs(self.contacts) do
		c:pre_solve(dt)
		-- multiple iterations
		-- required to fix deep contacts
		for i=1,5 do
			c:solve()
		end
	end
	
	-- move bodies
	for _,a in pairs(physic_actors) do
		a:integrate(dt)
	end
end

-- camera
function make_cam(f)
	local c={
		pos={0,6*hscale,0},
		lookat={0,0,-7*16},
		focal=f,
		dist=shl(5,ground_shift),
		-- camera rotation
		c=1,s=0,
		track=function(self,pos,angle)
			self.pos=v_clone(pos)
			self.lookat=v_clone(pos)
			self.c,self.s=cos(angle),-sin(angle)
			v_add(self.pos,{0,self.dist*self.s,self.dist*self.c})
		end,
		project=function(self,x,y,z)
			x-=self.lookat[1]
			local tmpy=y
			-- fake 3d
			y=-self.lookat[2]
			z-=self.lookat[3]
			z,y=self.c*z+self.s*y,-self.s*z+self.c*y

  	local xe,ye,ze=x,y,z-self.dist

		 local w=-self.focal/ze
  	return 64+xe*w,64-(tmpy+ye)*w,ze,w
		end
	}
	return c
end

-- particles
_g.update_part=function(self)
	if(self.t<time_t or self.r<0) return false
	-- gravity
	v_add(self.v,v_grav,self.g_scale)
	-- update pos
	local p=self.pos
	v_add(p,self.v,0.1)
	-- ground collision
	local h=get_altitude(p[1],p[3])
	if p[2]<h then
		p[2]=h
		-- todo: proper reflection vector
		v_scale(self.v,0.8)
	end
	
	-- force damping
	v_scale(self.v,self.dv)
	
	self.r+=self.dr
	-- animation frame
	self.frame+=self.df
	
	return true
end

_g.draw_part=function(self)
	local x,y,z,w=cam:project(self.pos[1],self.pos[2],self.pos[3])
	-- behind camera
	if(z>=0) return
	
	-- simple part
	if self.kind==0 then
	 -- fire smoke
		local s=flr(6*self.frame)
		local c0,c1=sget(s,2),sget(max(s-1),2)
		fillp(lerparray(dither_pat,1-self.frame)+0x0.f)
		circfill(x,y,w*self.r,bor(shl(c1,4),c0))
		fillp()
	end
end

all_parts=json_parse'{"smoke":{"rnd":{"r":[0.1,0.2],"c":[5,6,7],"dly":[12,18],"g_scale":[-0.03,-0.05]},"frame":0,"dv":0.9,"dr":0.05,"kind":0}}'

function make_part(part,p,v)
	local pt=add(parts,clone(all_parts[part],{pos=v_clone(p),v=v and v_clone(v) or v_zero(),draw=_g.draw_part,c=c}))
	pt.t,pt.update=time_t+pt.dly,pt.update or _g.update_part
	pt.df=1/pt.dly
	if(pt.sfx) sfx_v(pt.sfx,p)
	return pt
end

-- map helpers (marching codes, height map, normal map cache)
local qmap,hmap,ncache={},{},{}
function safe_index(i,j)
	return bor(band(i,0x7f),shl(band(j,0x7f),7))
end
function get_raw_qcode(i,j)
	return qmap[safe_index(i,j)]
end
function get_height(i,j)
	-- already scaled
	return hmap[safe_index(i,j)]
end
function get_q_colors(q)
	return shl(band(0x0.00ff,q),16),shl(band(0x0.ff00,q),8),shr(band(0xf00,q),8)
end

function get_altitude(x,z)
	-- cell
	local dx,dz=shr(x%ground_scale,ground_shift),shr(z%ground_scale,ground_shift)
	local i,j=flr(shr(x,ground_shift)),flr(shr(z,ground_shift))
	local h0,h1
	if dx>dz then
		local h=get_height(i,j)
		h0,h1=lerp(h,get_height(i+1,j),dz),lerp(h,get_height(i+1,j+1),dx)
	else
		local h=get_height(i+1,j+1)
		h0,h1=lerp(get_height(i,j),h,dz),lerp(get_height(i,j+1),h,dx)
	end
	return lerp(h0,h1,dz)
end


-- get map normal
function get_normal(x,z)
	local dx,dz=shr(x%ground_scale,ground_shift),shr(z%ground_scale,ground_shift)
	local i,j=flr(shr(band(x,0x7f),ground_shift)),flr(shr(band(z,0x7f),ground_shift))
	local h=hmap[safe_index(i,j)]
	if dx>dz then
		local n0=make_v_cross(
			{ground_scale,hmap[safe_index(i+1,j+1)]-h,ground_scale},
			{ground_scale,hmap[safe_index(i+1,j)]-h,0})
		v_normz(n0)
		return n0
	end	
	local n1=make_v_cross(
		{0,hmap[safe_index(i,j+1)]-h,ground_scale},
		{ground_scale,hmap[safe_index(i+1,j+1)]-h,ground_scale})
	v_normz(n1)
	return n1
end

function draw_tex_quad(a,b,sx,sy)
	palt(14,true)
	palt(0,false)
	local t,invdx,wa,wb=0,1/(b[2]-a[2]),a[4],b[4]
	for y=a[2],b[2] do
		local x,w=lerp(a[1],b[1],t),lerp(wa,wb,t)
		-- persp correction
		local u=t*wb/w
		sspr(sx,sy+16*u,16,1,x,y,shl(w,ground_shift),1)
		t+=invdx
	end
	palt()
end

function draw_htex_quad(a,b,sx,sy)
	local t,invdy,wa,wb=0,1/(b[1]-a[1]),a[4],b[4]
	for x=a[1],b[1] do
		local y,w=lerp(a[2],b[2],t),lerp(wa,wb,t)
		-- persp correction
		local v=t*wb/w
		sspr(sx+16*v,sy,1,16,x,y-shl(w,1),1,shl(w,1))
		t+=invdy
	end
end


-- draw actors on strip j
function draw_actors(j)
	local bucket=zbuf[band(j-1,0x7f)]
	if bucket then
		for _,d in pairs(bucket) do
			d=d.obj
			
			-- draw shadow
			if (d.draw_shadow) d:draw_shadow()
			d:draw()
		end
	end
end

function update_ground()
	local pos=plyr and plyr.pos or cam.lookat
	
	local i0,j0=flr(shr(pos[1],ground_shift)),flr(shr(pos[3],ground_shift))
	for i=i0-6,i0+6 do
		local cx=band(i,0x7f)
		for j=j0-7,j0+5 do
			local cy=band(j,0x7f)
			local t=ground_actors[cx+cy*128]
			if t then
				t:update(i,j)
				add(active_ground_actors,t)
			 add(drawables,t)
			end
		end
	end
end

function draw_ground(self)
	local imin,imax=-6,6
	local cx,cz=cam.lookat[1],cam.lookat[3]
	-- cell x/z ratio
	local dx,dz=cx%ground_scale,cz%ground_scale
	-- cell coordinates
	local nx,ny=flr(shr(cx,ground_shift)),flr(shr(cz,ground_shift))
	
	-- project anchor points
	local p={}
	-- grid depth extent
	for j=-7,5 do
	 -- project leftmost grid points
		local x,y,z,w=cam:project(-dx+cx+shl(imin,ground_shift),0,-dz+cz+shl(j,ground_shift))
		add(p,{x,y,z,w,ny+j})
	end
	
	-- move to 0-1 range
	dx/=ground_scale
	dz/=ground_scale
	
	local v0=p[1]
	local w0,nj=v0[4],v0[5]
	local dw0=shl(w0,ground_shift)
	for j=2,#p do
		local v1=p[j]
		local w1=v1[4]
		local dw1=shl(w1,ground_shift)
		local x0,x1=v0[1],v1[1]
		local x2,x3=v1[1]+dw1,v0[1]+dw0
		
		-- offset to grid space
		local ni=nx+imin
		local h0,h1=get_height(ni,nj),get_height(ni,nj+1)
		local y0,y1=flr(v0[2]-w0*h0),flr(v1[2]-w1*h1)
		for i=imin,imax do
			local q=get_raw_qcode(ni,nj)
			local h2,h3=get_height(ni+1,nj+1),get_height(ni+1,nj)
			local y2,y3=flr(v1[2]-w1*h2),flr(v0[2]-w0*h3)

		 -- in screen tile?
		 if x3>0 then
 		 -- left/right cliping

 		 if i==imin then
 			 x0,y0=lerp(x0,x3,dx),lerp(y0,y3,dx)
 				x1,y1=lerp(x1,x2,dx),lerp(y1,y2,dx)
 			elseif i==imax then
 				x3,y3=lerp(x0,x3,dx),lerp(y0,y3,dx)
 				x2,y2=lerp(x1,x2,dx),lerp(y1,y2,dx)
 			end
    
 			-- depth cliping
 			--[[
 			if j==2 then
 				x0,y0=lerp(x0,x1,dz),lerp(y0,y1,dz)
 				x3,y3=lerp(x3,x2,dz),lerp(y3,y2,dz)
 			elseif j==#p then
 				x1,y1=lerp(x0,x1,dz),lerp(y0,y1,dz)
 				x2,y2=lerp(x3,x2,dz),lerp(y3,y2,dz)
 			end
 			]]
 			
 			local c_hi,c_lo,c_dither=get_q_colors(q)
 			fillp(dither_pat2[c_dither])
 			
 			local q_code=band(q,0xf)
 			if q_code==1 or q_code==4 then
 				trifill(x0,y0,x2,y2,x1,y1,c_hi)
 				trifill(x0,y0,x2,y2,x3,y3,c_lo)

				 if c_hi!=c_lo then
						draw_htex_quad({x0,y0,0,w0},{x2,y2,0,w1},40,16)
					end
 			elseif q_code==9 then
 				draw_tex_quad({x0,y0,0,w0},{x1,y1,0,w1},c_hi,c_lo)
 			else
	 			trifill(x1,y1,x3,y3,x0,y0,c_hi)
	 			trifill(x1,y1,x3,y3,x2,y2,c_lo)
				 if c_hi!=c_lo then
						draw_htex_quad({x1,y1,0,w1},{x3,y3,0,w0},40,16)
					end
				end
			end
				
			-- no need to go further, tile is not visible
			if(x0>127) break
			
			x0,y0,x1,y1=x3,y3,x2,y2
			x2+=dw1
			x3+=dw0

			ni+=1
		end		
		
		fillp()
		draw_actors(nj)
		
		v0,w0,dw0=v1,w1,dw1
		nj+=1
	end
	-- last strip
	draw_actors(nj)
end

function _update()
	time_t+=1

 screen_update()

	zbuf_clear()
	
	if plyr then
		plyr:control()
	end

 -- update active ground objects	
	update_ground()
	
	-- physic update
	world:update()
	
	-- game logic update
	zbuf_filter(actors)
	zbuf_filter(parts)
	
	if plyr then
				-- do not track dead player
		if not plyr.disabled then
			-- update cam
			local lookat=v_clone(plyr.pos)
			v_add(lookat,m_fwd(plyr.m),3)
			-- keep altitude
			lookat[2]=plyr.pos[2]+2
			cam:track(lookat,0.15)
		end
	end
 
end

function draw_vector(m,p,v,c)
	v=v_clone(v)	
	v_add(v,p)	
	local x0,y0,z0,w0=cam:project(v[1],v[2],v[3])
	local x1,y1,z1,w1=cam:project(p[1],p[2],p[3])
	line(x0,y0,x1,y1,c)
end

function _draw()
	cls(0)

	zbuf_sort()
	draw_ground()

	--[[	
	for _,a in pairs(physic_actors) do
		a.bbox:draw(a.m,a.pos)
	end
	]]
	
	--[[
	for _,c in pairs(world.contacts) do
		local x,y,z,w=cam:project(c.p[1],c.p[2],c.p[3])
  
		circ(x,y,3,8)
		print(c.dv,x+2,y,7)
	end
 ]]
 
	rectfill(0,0,127,8,8)
	print("mem:"..stat(0).." cpu:"..stat(1).."("..stat(7)..")",2,2,7)

	print(plyr.traction,2,18,7)	
	
	--[[
	-- debug
	if plyr then
		v_print(plyr.v,2,12,7)
		v_print(plyr.omega,2,19,7)
		
		print("pow:"..plyr.traction.."%",2,26,7)
		if plyr.turn_ratio then
			print("turn:"..plyr.turn_ratio,2,33,7)
			
			draw_vector(plyr.m,plyr.pos,plyr.desired_force,9)
			draw_vector(plyr.m,plyr.pos,plyr.turn_force,8)
		end
		draw_vector(plyr.m,plyr.pos,plyr.v,2)
	end
 ]]
	draw_vector(plyr.m,plyr.pos,get_normal(plyr.pos[1],plyr.pos[3]),12)
	draw_vector(plyr.m,plyr.pos,{0,get_altitude(plyr.pos[1],plyr.pos[3])-plyr.pos[2],0},13)
end

-- main

function _init()
	
	local idx_offsets=json_parse'[0,1,128,129]'
	local q_codes=json_parse'[[0,0,0,0],[0,0,1,0],[0,0,0,2],[0,0,0x45,0x45],[0,4,0,0],[2,0,0,8],[0,0x15,0,0x15],[2,5,5,5],[8,0,0,0],[0x35,0,0x35,0],[5,1,4,5],[5,1,5,5],[0x25,0x25,0,0],[5,5,5,8],[5,5,4,5],[5,5,5,5]]'
	
	-- temp array to store the 64x64 noise map
	local noise={}
	local get_noise=function(i,j)
		return noise[band(i,0x3f)+64*band(j,0x3f)+1]
	end
	-- returns whether value is above a given level
	local is_solid=function(i,j,level,margin)
		i-=32
		j-=32
		local d=sqrt(i*i+j*j)
		return abs(d-level)<=margin and 1 or 0
		--return get_noise(i,j)>level and 1 or 0
	end
	-- converts four corners into a single lookup index
	-- cf: https://en.wikipedia.org/wiki/marching_squares
	local marching_code=function(i,j,level,margin)
		return
		8*is_solid(i,j,level,margin)+
		4*is_solid(i+1,j,level,margin)+
		2*is_solid(i+1,j+1,level,margin)+
		is_solid(i,j+1,level,margin)
	end
	-- q binary layout
	-- 0x0f00: dither pattern
	-- 0x00ff: q code
	-- 0x0.00ff: lo color
	-- 0x0.ff00: hi color
	local set_q_colors=function(q,lo,hi,n)
		return bor(q,bor(shl(n,8),bor(shr(lo,16),shr(hi,8))))
	end
	
 local perlin="210000000000000000000000000000100000000000012344566788887788876453210000000000000000000000000010000000000001234455578887778987646542110000000000000000000000000000000000000012345556788777899763766421100000000000000000000000000000000000001234566778888888875377754320000000000000000000000000000000000000123466677899898876538876653110000000000000000000000000000000000012346667889889987643887776421000000000000000000000000000000000001224566788889998764488877643211000000000000000000000000000000000112345577788999865447887775432110000000000000000000000000000000011123457888888876544788776654332100000000000000000000000000000011101235788777766544478876666554420000000000000000000000112210011211123577777766544337887666766542000000000000000000000012321222222112357777766654322777666777654210000000000000000000011233223322111246777776654432266667776655321000000000000000000000122222333222234677666665444336556776555532100000000000000000000001122233333323567766655334444446666655554221000000000000000000000000123443333456776554433566634666555565433210000000000000000000000002344433445666554444457763456654556544321000000000000000000000000123433333466665444446887334565455543333211111111100000000000000000122233334566544556788823455543333344542221222210000000000000000011122223456655566788882345544333234555443333321000000000000000000111223345555556778998134544333223455555544542100000000000000000001222233455556678999813444333222345666665554210000000000000000000232333455556667888882334332221235666665555421000000000000000000123444456655566668888222322222223566665445542100000000000000001223455556655556655677801221112233455556544454211000000000000000123455556665555555456770000001234444445554444321100000000000000012345545555445554444666000000123444333455444311110000000000000001234444444444444444456600000012334432234444432100000000000000000123333334443333334445660000001223444322344543210111000100000000013444323333332122344555000001222333432234465432111100111000000112344442222222101223344400000223322233223456554222222221000011123334454332222100112223330000012322212222445665544333332100001223444455433322110111122333000001332221112235566554444432100001223444555665543321111101233300000133222112234555554444443220000233344566667776554211122223230000012233211234555554334454443211234444567888999876543333333334000001223211122344443333445555442234555568899baa99876544444444450000012232122222333322344566666544455556789aabba9988765555566556000001233322112222222234678888866666666789aabbbaa9876655555677660000012333221111212223357789aa98777887899aabbbaaa986554455577777000011233321111111112235779aaaa9899a99aaabbbcbaa98754555566777780000122332222221111112457899abbbaabbbbbbcccddcba97644566677677870001233333332221111001357899abbccccdccccdeeedcba876445666776677700013443323222221110024579aaabbccddeddddeffedcba875445666766667700002444322222222111124689aabcccdeeedddeeffedcb9865445666566776600001344322222111111234689abcddddeeddddeeeedcba9865455665567776600112344322222221101234789bcdddcddccccdddeddcb9876544555456776650111233322222232111124579abcdddddccbbbcccdedca9876544454456777650112223321122222222235689bbccddddccbbbbbcdedca9876655444456666540012222211112233333456789bbccccdddcbbbbbcdddca987665544445555543000112210001123444556789aaabbbccddcbbaaabcccba887655554344444432000001110001223456778999aa999abbdccba9aabbbba9877655554443332222000000000001235667899999998889abcccba99aaaa98877665555433222111100000000011234667899aa987778899abcbba99999976665555434422101110000000000122234578999aa9876777899abbba99aa8766544444433321100000000000000122234578899a9987666678899aa99aa98665433444333331000011200000001222334677889aaa9766667778998899a976643223333443310000123000000012334456777899aa9876666668888899a987643221223443221000233000000013445666777899aaa98765555778899aa98765332112344321100023300000002356777777889999999765445778899aaa8766432112333211001123300000002468898778888889998765445677789aaa876654211222222101222330000000247899998998777898877644567789aaaa987653222122333222222210000001357899aa9998766788765544578889aaa998765433322233333322210000000247889abba988765677655444678889aaa988765444433334444321100"
	-- uncompress map
	for i=1,#perlin do
		local c=tonum("0x"..sub(perlin,i,i))
		add(noise,c)
	end
	
	for i=0,63 do
		for j=0,63 do
			--noise[band(i,0x3f)+64*band(j,0x3f)+1]=(j%8<4) and 2 or 0
		end
	end
	
	-- height map weights
	local hweights=json_parse'[[1,0,0,0],[0.5,0,0.5,0],[0.5,0.5,0,0],[0,0.5,0.5,0]]'
	-- explode the 64x64 map into 128x128
	for j=0,63 do
		for i=0,63 do
			local idx=2*i+2*128*j
			for k=1,4 do
				local w,k=hweights[k],idx+idx_offsets[k]
				
				local h=w[1]*get_noise(i,j)+w[2]*get_noise(i,j+1)+w[3]*get_noise(i+1,j)+w[4]*get_noise(i+1,j+1)
				hmap[k]=h/2
			end
		end
	end
	--[[
	for j=0,127 do
		for i=0,127 do
			local idx=safe_index(i,j)
			local h=hmap[idx]
			local n0=make_v_cross(
			{ground_scale,hmap[safe_index(i+1,j)]-h,0},
			{ground_scale,hmap[safe_index(i+1,j+1)]-h,ground_scale})
			v_normz(n0)
			local n1=make_v_cross(
			{0,hmap[safe_index(i,j+1)]-h,ground_scale},
			{ground_scale,hmap[safe_index(i+1,j+1)]-h,ground_scale})
			v_normz(n1)
			nmap[idx]={n0=n0,n1=n1}
		end
	end 
	]]	
	
	
	-- create multiple layers
	local layers=json_parse'[{"level":16,"margin":2,"hi":4,"lo":11},{"level":16,"margin":1.5,"hi":9}]'

	for l=1,#layers do
		local layer=layers[l]
		for j=0,63 do
			for i=0,63 do
				local q=marching_code(i,j,layer.level,layer.margin)
				local idx=2*i+2*128*j
				local code=q_codes[q+1]
				for k=1,4 do
					local q,k=code[k],idx+idx_offsets[k]
					-- hi/lo colors
					local hi,lo=layer.hi,layer.lo
					-- previous tile
					local prev_q=qmap[k]
					if prev_q then
						prev_hi,prev_lo=get_q_colors(prev_q)
						-- replace lo color
						lo=prev_lo
					end
					-- replace only full hi tiles
					prev_q=band(0xff,prev_q or 5)
					if prev_q==5 then
						if q==0 then
							hi,lo=lo,lo
						elseif band(0xf,q)==5 then
							hi,lo=hi,hi
						elseif q==1 or q==8 then
							hi,lo=hi,lo
						elseif q==4 or q==2 then
							hi,lo=lo,hi
						end
						q=set_q_colors(q,hi,lo,1)
						qmap[k]=q
					end
				end
			end
		end
	end
	
	local shade=function(lvl,c)
		return bor(shl(sget(max(lvl-1)+16,c),4),sget(lvl+16,c))
	end
	
	-- terrain shading
	for j=0,63 do
		for i=0,63 do
			local idx=2*i+2*128*j
			for k=1,4 do
				local k=idx+idx_offsets[k]
				-- tile
				local q=qmap[k]
				local hi,lo=get_q_colors(q)
				-- stripping pattern
				local strip=(j%2==0) and 0 or 1
				strip+=((i%2==0) and 0 or 1)
				hi,lo=shade(1,hi),shade(1,lo)
				qmap[k]=set_q_colors(band(0xff,q),hi,lo,1+strip)
			end
		end
	end

	-- textured strip demo
 local idx=safe_index(0,0)
	qmap[idx]=set_q_colors(9,24,0)
	for j=1,7 do
		local idx=safe_index(0,j)
		qmap[idx]=set_q_colors(9,24,16)
		for k=1,4 do
			hmap[idx+idx_offsets[k]]=2
		end
	end
	
	-- read models from gfx/map data
	unpack_models()

	local max_tree=1000
	for j=0,63 do
		for i=0,63 do
			local di,dj=i-32,j-32
			local d=abs(sqrt(di*di+dj*dj)-11)
			if flr(d)==2 then
				if rnd()>0.5 and max_tree>0 then --and is_solid(i,j,4)==1 then
					make_ground_actor("tree",2*i,2*j)
					max_tree-=1
				end
			end
		end
	end

	cam=make_cam(96)

	plyr=make_rigidbody(make_actor("plyr",{32,4,32}),all_models["audi_bbox"])
	
end

-->8
-- trifill
function p01_trapeze_h(l,r,lt,rt,y0,y1)
 lt,rt=(lt-l)/(y1-y0),(rt-r)/(y1-y0)
 if(y0<0)l,r,y0=l-y0*lt,r-y0*rt,0 
	y1=min(y1,128)
	for y0=y0,y1 do
  rectfill(l,y0,r,y0)
  l+=lt
  r+=rt
 end
end
function p01_trapeze_w(t,b,tt,bt,x0,x1)
 tt,bt=(tt-t)/(x1-x0),(bt-b)/(x1-x0)
 if(x0<0)t,b,x0=t-x0*tt,b-x0*bt,0 
 x1=min(x1,128)
 for x0=x0,x1 do
  rectfill(x0,t,x0,b)
  t+=tt
  b+=bt
 end
end
function trifill(x0,y0,x1,y1,x2,y2,col)
 color(col)
 if(y1<y0)x0,x1,y0,y1=x1,x0,y1,y0
 if(y2<y0)x0,x2,y0,y2=x2,x0,y2,y0
 if(y2<y1)x1,x2,y1,y2=x2,x1,y2,y1
 if max(x2,max(x1,x0))-min(x2,min(x1,x0)) > y2-y0 then
  col=x0+(x2-x0)/(y2-y0)*(y1-y0)
  p01_trapeze_h(x0,x0,x1,col,y0,y1)
  p01_trapeze_h(x1,col,x2,x2,y1,y2)
 else
  if(x1<x0)x0,x1,y0,y1=x1,x0,y1,y0
  if(x2<x0)x0,x2,y0,y2=x2,x0,y2,y0
  if(x2<x1)x1,x2,y1,y2=x2,x1,y2,y1
  col=y0+(y2-y0)/(x2-x0)*(x1-x0)
  p01_trapeze_w(y0,y0,y1,col,x0,x1)
  p01_trapeze_w(y1,col,y2,y2,x1,x2)
 end
end

-->8
-- unpack models
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
	for i=1,unpack_int() do
		local c=unpack_int()
		s=s..sub(itoa,c,c)
	end
	return s
end
function unpack_models()
	-- for all models
	for m=1,unpack_int() do
		local model,name,scale={},unpack_string(),unpack_int()
		-- vertices
		model.v={}
		for i=1,unpack_int() do
			add(model.v,{unpack_float(scale),unpack_float(scale),unpack_float(scale)})
		end
		
		-- faces
		model.f={}
		for i=1,unpack_int() do
			local f={p0=unpack_int(),ni=i,vi={}}
			for i=1,unpack_int() do
				add(f.vi,unpack_int())
			end
			-- center point
			f.center={unpack_float(scale),unpack_float(scale),unpack_float(scale)}
			-- color
			f.c=unpack_int()
			-- double_sided?
			f.double_sided=unpack_int()==1
			add(model.f,f)
		end

		-- normals
		model.n={}
		for i=1,unpack_int() do
			add(model.n,{unpack_float(),unpack_float(),unpack_float()})
		end
		
		-- n.p cache	
		model.cp={}
		for i=1,#model.f do
			local f,n=model.f[i],model.n[i]
			add(model.cp,v_dot(n,model.v[f.p0]))
		end

		-- merge with existing model
		all_models[name]=clone(model,all_models[name])
	end
end

__gfx__
1ca9b345000151000000000077007700770077000000000000077777000000000000000000000000000000000000000000000000000000000000000000000000
0000000001dc7700010000007700770077007700000000007775eee7000000000000000000000000000000000000000000000000000000000000000000000000
4951600012e77700520000000077007700770077000000775e7eeee7000000000000000000000000000000000000000000000000000000000000000000000000
000000003333b7001300000000770077007700770000075eee5eeeee000000000000000000000000000000000000000000000000000000000000000000000000
000000002497a70024000000770077007700770000007eeeeeeeeeee000000000000000000000000000000000000000000000000000000000000000000000000
0000000015d767001500000077007700770077000007e7eeeeeeeeee000000000000000000000000000000000000000000000000000000000000000000000000
00000000156767005400000000770077007700770075ee7eeeeeeeee000000000000000000000000000000000000000000000000000000000000000000000000
0000000015566700670000000077007700770077007eeeeeeeeeeeee000000000000000000000000000000000000000000000000000000000000000000000000
5c0000002288ee00280000000000000000000000075eeeeeeeeeeeee000000000000000000000000000000000000000000000000000000000000000000000000
00000000499ffa0054000000000000000000000007eeeeeeeeeeeeee000000000000000000000000000000000000000000000000000000000000000000000000
0000000099aaa7009a00000000000000000000000775eeeeeeeeeeee000000000000000000000000000000000000000000000000000000000000000000000000
0000000055533b003b000000000000000000000075eeeeeeeeeee555000000000000000000000000000000000000000000000000000000000000000000000000
000000001dcc7c001c00000000000000000000007eeeeeeeeeee5666000000000000000000000000000000000000000000000000000000000000000000000000
00000000115dd6001d00000000000000000000007eeeeeeeeee56666000000000000000000000000000000000000000000000000000000000000000000000000
000000001122ee002e00000077777777777777777eeeeeeeeee56666000000000000000000000000000000000000000000000000000000000000000000000000
0000000022eeff00ef0000007777777777777777777eeeeeeee56666000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000006666666666666666000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000005555555555555555000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000000001100000011000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000000005500000055000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000006666666666666666000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000007700000005555555555555555000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000001100000011000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000005500000055000000000000000000000000000000000000000000000000000000000000000000000000000
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
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
3040c002f04110c4693886a63886a6380969380969d886a6d886a6d80969d809d6386a39386ad6a86a39a86a6938d5a638d569a8d5a6a8d5196917f66917f669
b81969b839d786d6d786d6d70939d70907e7ba09e7ba39d7f5d6d7f547386a47a86ad8386ad8a86a0738d507a8d509a8d50938d5a6d8b7f669b769d8b71969b7
692946a62946693995a6399589f7e689b7d689978689b74689f7268938468958868938d689f7b989b79989975989b71989f7f889381989585989389986f7e686
b7d686978686b74686f7268638468658868638d686f7b986b79986975986b71986f7f886381986585986389972e040e02061c1b6083670008040807031410819
e8c000a040a04081a13908d9700020502060527030a688c7900070607080c002e1b008b8b99000505050104080726988c79000904090b0e1d107686aa0008040
8040a0c05978b99000d060d04212e0c1b10808e5700030403070b090b678b99000d040d0f032423968d5800050605060012232f008b836700060406020e001a6
7836900010401050f0d0697836900011601182413162210869e790005040507282114909377000704070526231c61948c0006040605011210819c6c000514051
61718108d7c7500061406151b1c108d74650008140817191a108d7d95000204020307161b608c770004040401051815908c77000906090d1f1a0a19108188a70
00304030909171d608d97000104010d0b1515908367000d140d1e102f108686a5000f140f102c0a009686aa0001240122201e0d668d580004240423222120868
d55000624062526021c609377000824082728041491948c000f040f05092b269f806901060406001c2a2a6f8069010924092a2c2b20839f59010e280e2d24333
231303f289f786001063806353c3b3a393837389f7590010d380d3e3f3041424344486f786001054805464748494a4b4c486f7590010723627080819b9d93748
060808080a580a080808080a0a084808572606084808080608f9870608080a0808080a08c90908460908087996080608080608080628362708d9270808599936
3748d9270808080a08080a080806080806460908c909080a0808060808080a280a08080a080806080806080890c002f04110d0d0a1321080f667d52729d5f667
9a27290a1967d5e829d519679ae8290a60104010204030173818000030403040807008385a0000704070806050f8381800005040506020100838d50000304030
70501008673800008040804020600829f700006006480808a8f90a4808080806080608080a0840f1d1010130b068083808c8080808a7086a08a7083808a8f8d8
a88737a8870808f8d808873708877010301020302848f740003030302050e748f74000603060407048492830005030502010084828400070307040800849b730
008030804060c749283000b030b0a090080808000070b98817568817b988f80888f90888165688f8080a08000000000000000000000000000000000000000000
__sfx__
000200090765006650066500665006650306500565005650056500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

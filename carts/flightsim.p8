pico-8 cartridge // http://www.pico-8.com
version 16
__lua__
-- xwing vs. tie figther
-- by freds72

-- game globals
local time_t,good_side,bad_side=0,0x1,0x2

-- register json context here
function nop() return true end

-- player
local plyr
local actors={}
-- ground constants 
local ground_shift,ground_colors,ground_level=2,{1,13,6}


-- zbuffer (kind of)
local drawables={}
function zbuf_clear()
	drawables={}
end
function zbuf_draw()
	local objs={}
	for _,d in pairs(drawables) do
		local p=d.pos
		local x,y,z,w=cam:project(p[1],p[2],p[3])
		-- cull objects too far
		if z>-3 then
			add(objs,{obj=d,key=z,x=x,y=y,z=z,w=w})
		end
	end
	-- z-sorting
	sort(objs)
	-- actual draw
	for i=1,#objs do
		local d=objs[i]
		d.obj:draw(d.x,d.y,d.z,d.w)
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
function lerparray(a,t)
	return a[mid(flr((#a-1)*t+0.5),1,#a)]
end

-- https://github.com/morgan3d/misc/tree/master/p8sort
function sort(data)
 for num_sorted=1,#data-1 do 
  local new_val=data[num_sorted+1]
  local new_val_key,i=new_val.key,num_sorted+1

  while i>1 and new_val_key>data[i-1].key do
   data[i]=data[i-1]   
   i-=1
  end
  data[i]=new_val
 end
end

-- edge cases:
-- a: -23	-584	-21
-- b: 256	-595	256
function sqr_dist(a,b)
	local dx,dy,dz=b[1]-a[1],b[2]-a[2],b[3]-a[3]
	if abs(dx)>128 or abs(dy)>128 or abs(dz)>128 then
		return 32000
	end
	local d=dx*dx+dy*dy+dz*dz 
	-- overflow?
	return d<0 and 32000 or d
end

-- world axis
local v_fwd,v_right,v_up={0,0,1},{1,0,0},{0,1,0}

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

-- matrix functions
function m_x_v(m,v)
	local x,y,z=v[1],v[2],v[3]
	v[1],v[2],v[3]=m[1]*x+m[5]*y+m[9]*z+m[13],m[2]*x+m[6]*y+m[10]*z+m[14],m[3]*x+m[7]*y+m[11]*z+m[15]
end
function m_x_xyz(m,x,y,z)		
	return
		m[1]*x+m[5]*y+m[9]*z+m[13],
		m[2]*x+m[6]*y+m[10]*z+m[14],
		m[3]*x+m[7]*y+m[11]*z+m[15]
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
		1-(yy+zz),xy+wz,xz-wy,0,
		xy-wz,1-(xx+zz),yz+wx,0,
		xz+wy,yz-wx,1-(xx+yy),0,
		0,0,0,1
	}
end

-- only invert 3x3 part
function m_inv(m)
	m[2],m[5]=m[5],m[2]
	m[3],m[9]=m[9],m[3]
	m[7],m[10]=m[10],m[7]
end
function m_set_pos(m,v)
	m[13],m[14],m[15]=v[1],v[2],v[3]
end
-- returns foward vector from matrix
function m_fwd(m)
	return {m[9],m[10],m[11]}
end
-- returns up vector from matrix
function m_up(m)
	return {m[5],m[6],m[7]}
end
-- right vector
function m_right(m)
	return {m[1],m[2],m[3]}
end

-- models
-- models
local all_models={
	landing_strip={
		c=6,
		v={{-1,0,0}, --points
			{-1,0,30},
			{1,0,30},
			{1,0,0},
			{0,0,20},
			{0,0,17},
			{0,0,15},
			{0,0,12}},
		e={{1,2}, --lines
			{2,3},
			{3,4},
			{4,1},
			{5,6},
			{7,8}
		}
	}
}

function draw_actor(self,x,y,z,w)	
	-- distance culling
	draw_model(self.model,self.m,x,y,z,w)
end

-- little hack to perform in-place data updates
local draw_session_id=0
local znear,zdir=3,-1
function draw_model(model,m,x,y,z,w)
	draw_session_id+=1

	color(model.c)

	-- edges
	local p={}
	for _,e in pairs(model.e) do	
		-- edges indices
		local ak,bk=e[1],e[2]
		-- edge positions
		local a,b=p[ak],p[bk]
		-- not in cache?
		if not a then
			local v=make_v(cam.pos,model.v[ak])
			m_x_v(cam.m,v)
			a,p[ak]=v,v
		end
		if not b then
			local v=make_v(cam.pos,model.v[bk])
			m_x_v(cam.m,v)
			b,p[bk]=v,v
		end
		-- line clipping aginst near cam plane
		-- swap end points
		if(a[3]<b[3]) a,b=b,a
		local s=make_v(a,b)
		local den=zdir*s[3]
		if a[3]>znear and b[3]<znear then
			local t=zdir*(znear-a[3])/den
			if t>=0 and t<=1 then
				-- intersect pos
				v_scale(s,t)
				v_add(s,a)
				local x0,y0=cam:project2d(a)
				local x1,y1=cam:project2d(s)
				line(x0,y0,x1,y1,1)
				pset(x1,y1,8)
			end
		elseif b[3]>znear then
			local x0,y0=cam:project2d(a)
			local x1,y1=cam:project2d(b)
			line(x0,y0,x1,y1,1)
		end
	end
end

function plane_ray_intersect(n,p,a,b)
	local r=make_v(a,b)
	local den=v_dot(r,n)
	-- no intersection
	if abs(den)>0.001 then
		local t=v_dot(make_v(a,p),n)/den
		if t>=0 and t<=1 then
			-- intersect pos
			v_scale(r,t)
			v_add(r,a)
			return r
		end
	end
end

draw_plyr=function(self,x,y,z,w)
	-- draw_model(self.model,self.m,x,y,z,w)
end

update_plyr=function(self)
	-- damping
	self.roll*=0.8
	self.pitch*=0.85
	return true
end

local all_actors={
	tower={
		model=all_models.tower,
		update=nop
	},
	landing={
		model=all_models.landing_strip,
		update=nop
	}
}

function make_plyr(x,y,z)
	local p={
		acc=0.2,
		pos={x,y,z},
		q=make_q(v_fwd,0),
		roll=0,
		pitch=0,
		draw=nop,
		update=update_plyr
	}
	local m=m_from_q(p.q)
	m_set_pos(m,p)
	p.m=m
	add(actors,p)
	return p
end

function make_actor(src,p)
	-- instance
	local a=clone(src,{
		pos=v_clone(p),		
		q=make_q(v_up,0)
	})
	a.draw=a.draw or draw_actor
	-- init orientation
	local m=m_from_q(a.q)
	m_set_pos(m,p)
	a.m=m
	return add(actors,a)
end

function make_cam(x0,y0,focal)
	local c={
		pos={0,0,3},
		q=make_q(v_up,0),
		update=function(self)
			self.m=m_from_q(self.q)
			m_inv(self.m)
		end,
		track=function(self,pos,q)
			self.pos,q=v_clone(pos),q_clone(q)
			self.q=q
		end,
		project=function(self,x,y,z)
			-- world to view
			x-=self.pos[1]
			y-=self.pos[2]
			z-=self.pos[3]
			x,y,z=m_x_xyz(self.m,x,y,z)
			-- too close to cam plane?
			if(z<0.001) return nil,nil,-1,nil
			-- view to screen
	 		local w=focal/z
 			return x0+x*w,y0-y*w,z,w
		end,
		-- project cam-space points into 2d
		project2d=function(self,v)
			-- view to screen
 			local w=focal/v[3]
 			return x0+v[1]*w,y0-v[2]*w
		end
	}
	return c
end

function draw_ground(self)

	-- draw horizon
	local zfar=-96
	local x,y=-64*zfar/64,64*zfar/64
	local farplane={
			{x,y,zfar},
			{x,-y,zfar},
			{-x,-y,zfar},
			{-x,y,zfar}}
	-- ground point in cam space	
	local p={0,cam.pos[2],0}
	m_x_v(cam.m,p)

	-- ground normal in cam space
	local n={0,1,0}
	m_x_v(cam.m,n)

	local v0=farplane[#farplane]
	local horiz={}
	for i=1,#farplane do
		local v1=farplane[i]
		local s=plane_ray_intersect(n,p,v0,v1)
		if(s) add(horiz,s)
		v0=v1
	end
	
	-- view frustrum
	--[[
	local x0,y0=cam:project2d(farplane[#farplane])
	for i=1,#farplane do
		local x1,y1=cam:project2d(farplane[i])
		line(x0,y0,x1,y1,1)
		x0,y0=x1,y1
	end
	]]
	
	-- complete line?
	if #horiz==2 then
		local x0,y0=cam:project2d(horiz[1])
		local x1,y1=cam:project2d(horiz[2])
		line(x0,y0,x1,y1,3)
	end

	local cy=cam.pos[2]

	local scale=4*max(flr(cy/32+0.5),1)
	scale*=scale
	local x0,z0=cam.pos[1],cam.pos[3]
	local dx,dy=x0%scale,z0%scale
	
	for i=-4,4 do
		local ii=scale*i-dx+x0
		for j=-4,4 do
			local jj=scale*j-dy+z0
			local x,y,z,w=cam:project(ii,0,jj)
			if z>0 then
				pset(x,y,3)
			end
 	end
	end
end

-- handle player inputs
function control_plyr(self)
	
	local pitch,roll,input=0,0,false
	if(btn(0)) roll=1 input=true
	if(btn(1)) roll=-1 input=true
	if(btn(2)) pitch=-1
	if(btn(3)) pitch=1
		 		
	self.roll+=roll
	self.pitch+=pitch
	
	local q=make_q(m_right(plyr.m),-self.pitch/256)
	q_x_q(q,make_q(m_fwd(plyr.m),self.roll/256))
	q_x_q(q,plyr.q)
	local m=m_from_q(q)
	local fwd=m_fwd(m)
	v_add(self.pos,fwd,self.acc)

	m_set_pos(m,self.pos)
	self.m,self.q=m,q
end

-- play loop
function _update60()
	time_t+=1

	zbuf_clear()
	
	control_plyr(plyr)

	-- update cam
	cam:track(plyr.pos,plyr.q)
	
	zbuf_filter(actors)
	
	-- must be done after update loop
	cam:update()
end

function _draw()
	cls()

 -- draw horizon
	-- todo
	
	--clip(0,0,128,32)
	draw_ground()	
	zbuf_draw()
	--clip()
	
	-- draw cockpit
end

function _init()

	cam=make_cam(64,64,64)

	make_actor(all_actors.landing,{0,0,0})
	plyr=make_plyr(0,5,-10)
end


-->8
-- stats
--[[
local cpu_stats={}

function draw_stats()
	-- 
	fillp(0b1000100010001111)
	rectfill(0,0,127,9,0x10)
	fillp()
	local cpu,mem=flr(100*stat(1)),flr(100*(stat(0)/2048))
	cpu_stats[time_t%128+1]={cpu,mem}
	for i=1,128 do
		local s=cpu_stats[(time_t+i)%128+1]
		if s then
			-- cpu
			local c,sy=11,s[1]
			if(sy>100) c=8 sy=100
			pset(i-1,9-9*sy/100,c)
		 -- mem
			c,sy=12,s[2]
			if(sy>90) c=8 sy=100
			pset(i-1,9-9*sy/100,c)
		end
	end
	if time_t%120>60 then
		print("cpu:"..cpu.."%",2,2,7)
	else
		print("mem:"..mem.."%",2,2,7)
	end
end
]]


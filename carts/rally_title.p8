pico-8 cartridge // http://www.pico-8.com
version 18
__lua__
-- ghost rally
-- by @freds72
-- title screen

-- globals
local time_t,time_dt=0,1/30
local actors,ground_actors,parts,v_light,cam,plyr,active_ground_actors={},{},{},{0,1,0}

function nop() return true end

-- world units
local ground_shift,hscale=1,4
local ground_scale=2^ground_shift
local ground_left,ground_right,ground_far,ground_near=-7,7,5,-7
local v_grav={0,-1,0}
-- transitions mgt
local draw_state,update_state=nop,nop

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
function acos(c)
 return atan2(c,sqrt(1-c*c))
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
function m_inv_x_v(m,v,p)
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

-- model bounding box
function get_modelsize(model)
	local vmin,vmax={32000,32000,32000},{-32000,-32000,-32000}
	for _,v in pairs(model.v) do
		vmin,vmax=v_min(vmin,v),v_max(vmax,v)
	end
 return make_v(vmin,vmax)
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
	for i=1,#model.f do
		local f,n=model.f[i],model.n[i]
		-- viz calculation
		if v_dot(n,cam_pos)>=model.cp[i] then
			-- project vertices
			for _,vi in pairs(f.vi) do
				if not p[vi] then
					local v=m_x_v(m,model.v[vi])
					v_add(v,pos)
					local x,y,z,w=cam:project(v)
					-- avoid rehash for u/v
					p[vi]={x,y,0,0}
				end
			end
			-- distance to camera (in object space)
			local d=sqr_dist(f.center,cam_pos)

			-- register faces
			add(faces,{key=d,face=f})
		end
	end

 if not outline then
		-- sort faces
		sort(faces)
	end
	
	-- draw faces using projected points
	for _,f in pairs(faces) do
		f=f.face
		local p0,uv0=p[f.vi[1]],f.uv[1]
		p0[3],p0[4]=uv0[1],uv0[2]
		for i=2,#f.vi-1 do
			local p1,p2=p[f.vi[i]],p[f.vi[i+1]]
			if outline then
				fillp(0xf0f0.f)
				trifill(p0[1],p0[2],p1[1],p1[2],p2[1],p2[2],0x1)
				fillp()
			else
				local uv1,uv2=f.uv[i],f.uv[i+1]
				p1[3],p1[4]=uv1[1],uv1[2]
				p2[3],p2[4]=uv2[1],uv2[2]
				tritex(p0,p1,p2)
			end
		end	
	end
end

function draw_model_shadow(model,m,pos)
	-- fillp(0xa5a5.f)
	-- v_light dir in object space
	local l=v_clone(v_light)
	m_inv_x_v(m,l)
	
	-- faces
	local p={}
	for i=1,#model.f do
		local f,n=model.f[i],model.n[i]
		-- viz calculation
		if v_dot(n,l)<0 then
			-- project vertices
			for _,vi in pairs(f.vi) do
				if not p[vi] then
					local v=m_x_v(m,model.v[vi])
					v_add(v,pos)
					v[2]=get_altitude_and_n(v)
					local x,y,z,w=cam:project(v)
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
	fillp()
end

local sa_curve,sr_curve
function apply_curve(curve,t)
	t=127*mid(t,0,1)
	return curve[flr(t)+1]/127
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

	local a={
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
		update=function(self)
			self.pos[1]+=0.5
			self.pos[3]+=0.5
			self.pos[2]=0.4+0.25*abs(cos(time_t/64))
 		if rnd()>0.5 then
 			local pos=self:pt_toworld({0,0,-1.8})
 			--add(pos,v_up)
 			make_part("smoke",pos)
 		end		
			return true
		end
	}
	return add(actors,a)
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

-- camera
function make_cam(focal)
	-- camera rotation
	local cc,ss=1,0
	local dist=shl(8,ground_shift)
	return {
		pos={0,6*hscale,0},
		lookat={0,0,-7*16},
		track=function(self,pos,angle,d)
			dist=d
			self.pos=v_clone(pos)
			self.lookat=v_clone(pos)
			cc,ss=cos(angle),-sin(angle)
			v_add(self.pos,{0,dist*ss,dist*cc})
		end,
		project=function(self,v)
			-- pitch 
			local x,y,z=v[1]-self.lookat[1],-self.lookat[2],v[3]-self.lookat[3]
			z,y=cc*z+ss*y,-ss*z+cc*y

			local xe,ye,ze=x,y,z-dist

			local w=-focal/ze
  			return 64+xe*w,64-(v[2]+ye)*w,ze,w
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
		-- todo: proper reflection vector
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
	elseif self.kind==3 then
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
	hit={
	  	rnd={
    	    dly={
                8,
                12
            }
     	},
     	g_scale=0,
     	kind=3
				},
    smoke={
        frames={
            3,
            19,
            20,
            4,4
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
	local pt=add(parts,clone(all_parts[part],{pos=v_clone(p),v=v and v_clone(v) or v_zero(),frame=0,draw=draw_part}))
	pt.t,pt.update=time_t+pt.dly,pt.update or update_part
	pt.df=1/pt.dly
	if(pt.sfx) sfx_v(pt.sfx,p)
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

local colors={11,4,9}
local shade=function(lvl,c)
	c=colors[c+1]
	return bor(shl(sget(max(lvl-1)+16,c),4),sget(lvl+16,c))
end

function draw_ground(self)
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
		local y0,y1=flr(v0[2]-w0*h0),flr(v1[2]-w1*h1)
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
			local y2,y3=flr(v1[2]-w1*h2),flr(v0[2]-w0*h3)

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
				
				local c_hi,c_lo,c_dither=shr(band(0b00111000,q0),3),band(0b111,q0)

				local strip=(nj%4<2) and 0 or 1
				strip+=((ni%4<2) and 0 or 1)
				c_hi,c_lo=shade(1,c_hi),shade(1,c_lo)

				fillp(dither_pat2[strip+1])

				if band(q0,0x40)>0 then
					trifill(x0,y0,x2,y2,x1,y1,c_hi)
					trifill(x0,y0,x2,y2,x3,y3,c_lo)
				else
					trifill(x1,y1,x3,y3,x0,y0,c_lo)
					trifill(x1,y1,x3,y3,x2,y2,c_hi)
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

-- game states
-- transition to next state
function next_state(state)
	draw_state,update_state=state()
end

function start_state()
	-- reset arrays & counters
	time_t,actors,ground_actors,parts,active_ground_actors=0,{},{},{},{}

	-- read track (drop)
	unpack_track()

	-- read actors
	unpack_actors()

	-- create selection object
	plyr=make_plyr({16,0.51,16},0.1)

	return 
		-- draw
		function()
			fillp(0xf0f0.ff)
			--rectfill(0,0,127,36,1)

			for i=0,13 do
				pal(13,rnd()>0.8 and 7 or 12)
				sspr(0,19+i,64,1,9,10+i)
				pal()
			end
			sspr(0,33,60,13,50,23)
			--[[
			for i=1,#dither_pat do
				fillp(dither_pat[i]+0x.ff)
				line(0,101+i,127,101+i,0)
			end
			]]
			fillp(0xf0f0.ff)
			rectfill(0,103,127,127,0x1)
			printb("205 gti 16s",44,106,7)
			if(time_t%48<24) printb("any key: start game",28,118,6)
			fillp()
		end,
		-- update
		function()
		end
end

function _update()
	time_t+=1

	-- basic state mgt
	update_state()
	
	zbuf_clear()
	
 	-- update active ground objects	
	update_ground()
	
	-- game logic update
	zbuf_filter(actors)
	zbuf_filter(parts)
	
	if plyr then
		-- update cam
		local lookat=v_clone(plyr.pos)
		v_add(lookat,m_fwd(plyr.m),1)
		-- keep altitude
		lookat[2]=plyr.pos[2]+2
		cam:track(lookat,0.10,7)
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
	for i=-1,1 do
		for j=1,2 do
			print(s,x+i,y+j,0)
		end
	end
	print(s,x,y+1,1)
	print(s,x,y,c)

end

function _draw()
	cls(0)

	zbuf_sort()
	draw_ground()
	
	draw_state()
	

	--rectfill(0,0,127,8,8)
	--print("mem:"..stat(0).." cpu:"..stat(1).."("..stat(7)..")",2,2,7)
 
 
end

function _init()
	-- read models from gfx/map data
	unpack_models()
	
	-- curves (dummy)
	unpack_bytes()
	unpack_bytes()

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
		
	cam=make_cam(96)
		
	-- init state machine
	next_state(start_state)
end

-->8
-- trifill
-- by @p01
function p01_trapeze_h(l,r,lt,rt,y0,y1)
 lt,rt=(lt-l)/(y1-y0),(rt-r)/(y1-y0)
 if(y0<0)l,r,y0=l-y0*lt,r-y0*rt,0 
	for y0=y0,min(y1,128) do
  rectfill(l,y0,r,y0)
  l+=lt
  r+=rt
 end
end
function p01_trapeze_w(t,b,tt,bt,x0,x1)
 tt,bt=(tt-t)/(x1-x0),(bt-b)/(x1-x0)
 if(x0<0)t,b,x0=t-x0*tt,b-x0*bt,0 
 for x0=x0,min(x1,128) do
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
			local f={ni=i,vi={},uv={}}
			-- vertex indices
			for i=1,unpack_int() do
				add(f.vi,unpack_int())
			end
			-- uv coords (if any)
			for i=1,unpack_int() do
				add(f.uv,{unpack_int(),unpack_int()})
			end
			-- center point
			f.center={unpack_float(scale),unpack_float(scale),unpack_float(scale)}
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
			add(model.cp,v_dot(n,model.v[f.vi[1]]))
		end
	
		-- merge with existing model
		all_models[name]=clone(model,all_models[name])
	end
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
function unpack_track()
	local track={}
	for k=1,unpack_int() do
	 -- +1 shift to center track marker
	local pos={shl(unpack_int()+1,ground_shift+1),0,shl(unpack_int()+1,ground_shift+1)}
		pos[2]=get_altitude_and_n(pos)
		add(track,{pos=pos})
	end
	return track
end
-- unpack int array
function unpack_actors()
	for k=1,unpack_int() do
		make_ground_actor(2*unpack_int(),2*unpack_int(),unpack_int())	 
	end
end
function unpack_bytes()
	local bytes={}
	for k=1,unpack_int() do
		add(bytes,unpack_int())
	end
	return bytes
end
-->8
-- trifilltex
-- 
function trapezefill(l,dl,r,dr,start,finish)
	-- layout:x y u v
	local l,dl={l[1],l[3],l[4],r[1],r[3],r[4]},{dl[1],dl[3],dl[4],dr[1],dr[3],dr[4]}
	local dt=1/(finish-start)
	for k,v in pairs(dl) do
		dl[k]=(v-l[k])*dt
	end

	-- cliping
	if start<0 then
		for k,v in pairs(dl) do
			l[k]-=start*v
		end
		start=0
	end

	-- rasterization
	for j=start,min(finish,127) do
		local len=l[4]-l[1]
		if len>0 then
			local u0,v0=l[2],l[3]
			local du,dv=(l[5]-u0)/len,(l[6]-v0)/len
			for i=l[1],l[4] do
				local c=sget(u0,v0)
				if(c!=11) pset(i,j,c)
				u0+=du
				v0+=dv
			end
  end 
		for k,v in pairs(dl) do
			l[k]+=v
		end
	end
end
function tritex(v0,v1,v2)
	local x0,x1,x2=v0[1],v1[1],v2[1]
	local y0,y1,y2=v0[2],v1[2],v2[2]
	if(y1<y0)v0,v1,x0,x1,y0,y1=v1,v0,x1,x0,y1,y0
	if(y2<y0)v0,v2,x0,x2,y0,y2=v2,v0,x2,x0,y2,y0
	if(y2<y1)v1,v2,x1,x2,y1,y2=v2,v1,x2,x1,y2,y1

	-- mid point
	local v02,mt={},1/(y2-y0)*(y1-y0)
	for k,v in pairs(v0) do
		v02[k]=v+(v2[k]-v)*mt
	end
	if(x1>v02[1])v1,v02=v02,v1

	-- note: no need to x/y optimize as we are drawing per pixel
	-- upper trapeze
	trapezefill(v0,v1,v0,v02,y0,y1)
	-- lower trapeze
	trapezefill(v1,v2,v02,v2,y1,y2)
end

__gfx__
000000000001510000000000eeeeeeeeeeeeeeeeeee0000000000000000000000000000bb88856599777777777777777777777777777777777777788756566bb
0000000001dc770001000000ee9994eeeeeeeeeeeee0000000000000000000000000000b888856599766666777777777711666667666677777777788756666bb
0000000012e7770052000000e999994eee99eeeeeee0000000000000000000000000000b8888565657666667777777777116666677777666666667aa756776bb
000000003333b70013000000e999994eee94eeeeeee0000000000000000000000000000b8888565657666667777777777116666677777777777776aa756776bb
000000002497a70024000000e499944eeeeeeeeeeee0000000000000000000000000000bb0555656586666677777777771166666777777887667765a756776bb
0000000015d7670015000000e444444eeeeee4eeeee0000000000000000000000000000bb0555656c866666777777777711666665777788877766656756556bb
000000001567670054000000ee4444eeeeeeeeeeeee0000000000000000000000000000bb505565cc866666777777777711666665777780877777656756666bb
000000001556670067000000eeeeeeeeeeeeeeeeeee0000000000000000000000000000bb055565cc866666777777777711666665777787877777656756556bb
000000002288ee0028000000eeeeeeeeeeeeeeeeeee0000000000000000000000000000bb505565ca766666777777777711666665777788877777656756666bb
00000000499ffa0054000000ee9994eeee994eeeeee0000000000000000000000000000bb056565aa766666777777777711666665777778877777656756556bb
0000000099aaa7009a000000e999994ee99994eeeee0000000000000000000000000000bb566565a1766666777777777711666665777777777777765756666bb
0000000055533b003b000000e999444ee49944eeeee0000000000000000000000000000bb50656511766666777777777711666665777777778877567756556bb
000000001dcc7c001c000000e4944eeeee444eeeeee0000000000000000000000000000bb56656511766666777777777711666665777778888877656756666bb
00000000115dd6001d000000e444eeeeeeeeeeeeeee0000000000000000000000000000bb05656518766666777777777711666665777788111177656756556bb
000000001122ee002e000000ee44ee94eeeee4eeeee0000000000000000000000000000bb5055658876666677777777771166666577778111aa77656756666bb
0000000022eeff00ef000000eeeeee44eeeeeeeeeee0000000000000000000000000000bb05556585788666777777777711666665777781aacc77656756556bb
000000000000000000000000eeeeeeeeeeeeeeeeeee0000000000000000000000000000bb50556565788866777777777711666665777781acc777656756666bb
000000000000000000000000eeeeeeeeeeeeeeeeeee0000000000000000000000000000bb05556565780866777777777711666665777781ac7766656756556bb
000000000000000000000000eeeeeeeeeeeeeeeeeee0000000000000000000000000000bb05556565787866777777777711666667777781a7667765a756776bb
00001111111110011111111111100000011111000000111111100111111111100000000b8888565657888667777777777116666677777777777776aa756776bb
0001ccddcccdc11ccddc11ccccc100011ccddc100011cccddcc11ccddccdccc10000000b8888565657886667777777777116666677777666666667aa756776bb
00111111111111111111111111110011111111110111111111111111111111110000000b888856599766666777777777711666667666677777777788756666bb
01cdccccddccc11ccccc11cdcdc101ccdddccdcc11cdcc11ccc11cddccccdcc10000000bb88856599777777777777777777777777777777777777788756566bb
11111111111111011111111111101111111111111111111111101111111111110000000bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
1cddcc1111111001cdddcccdcc101cdccc11cccdd1ccddccc1101dc1cdcc1cc10000000bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
11111111111111011111111111101111111111111111111111100111111111100000000bbbbbbbb7777777777777777777777777bbbbbbbbbbbbbbbbbbbbbbbb
1cccdc11cccdc101cdcc11cccc101ccdcc11cdccc1111ccdddc10111ccdc11100000000bbbbbbb777777666666676666666666667bbbbbbbbbbbbbbbbbbbbbbb
11111111111111011111111111101111111111111111111111110001111110000000000bbbbbb777887666666667666666666666676bbbbbbbbbbbbbbbbbbbbb
01cdccc11ccc101ccccc11ccdcd101cccccdddcc11dcc11cccc1001cccddc1000000000bbbbb7778aa86666666676677777666666676bbbbbbbbbbbbbbbbbbbb
01111111111110111111111111110111111111111111111111100011111111000000000bbbb77778aa866666666766766666666666676bbbbbbbbbbbbbbbbbbb
0011cdcccc11001ccdcc11ccdcc100111cdccc1101ccdccdc110001cdcccc1000000000bbb777777887666666667667777766666666676bbbbbbbbbbbbbbbbbb
00111111111100011111111111100001111111100011111111000001111110000000000bb77777777776666666676666666666666666776bbbbbbbbbbbbbbbbb
00001111110000011111111111100000011111000011111110000001111110000000000b77777777777777777777777777777777777777777777777777bbbbbb
07777777777000007777777700077777700000777777000007777707777000000000000777888888888888888777777777777777777888888888888888777bbb
07777777777700007777777700077777700000777777000007777707777000000000000778888111111111111177775575555555577711111111111888877777
17777777777770017777777710177777710001777777100017777717777100000000000558881111aaaaaaaaaaa77755575755757777aaaaaaaa111188887888
1677776667777001677677761016777761000167777610001677771777610000000000086688111aaaccccc6656677575757575557777ccccccaa111188878a8
1177771117777101777177771011777711000117777110001167771776110000000000086660055500ccccc66566777777777777777777cccccca00555007787
01777777777761007771777700017777100000177771000001177777711000000000000556055555550ccccc66566777777777777777777ccccc055555550777
017777777777110177777777100177771000001777710000001677776100000000000006605555555550cccc66566777878777787877777cccc0555555555055
017777667777100777666777700177771077701777710777001177771100000000000006655555755555cccccccccc778888888878777777ccc5555575555566
077777117777777777117777770777771077707777710777000777777000000000000006655556665555cccccccccc777777777777777777ccc5555666555566
077777716777777777107777770777777777717777777777100777777000000000000006655576667555ccccccccccc777777777777777777cc5557666755565
17777771167777777711777777177777777771777777777710177777710000000000000b655556665555ccccccccccc111111111111111111cc5555666555566
16666661116666666611666666166666666661666666666610166666610000000000000bb55555755555cccccccccccc111111111111111111c5555575555566
11111111011111111111111111111111111111111111111110111111110000000000000bbb555555555055555555555555555555555555555550555555555bbb
00000000000000000000000000000000000000000000000000000000000000000000000bbbb5555555bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb5555555bbbb
00000000000000000000000000000000000000000000000000000000000000000000000bbbbb55555bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb55555bbbbb
00000000000000000000000000000000000000000000000000000000000000000000000bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
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
206040207021f141100156f67456d874b9f674b9d87456f69956d899b9f699b9d89956f6fb5698fbb9f6fbb998fbb6b9e559b9e5b6b97859b978d04010206050
4074037402e602e6035607e740304020104074711571150074000874e7406080c0a040860086715771570008cab84030708040407403e603e6027402b907e740
90a0c0b040080057005771087108fbc7405060a09040e603e6020822080356cad7408070b0c040e602e60308030822b9cad7401090b0304026b2f6b2f6d226d2
0838f640d0e001f04085008571067106000837b940d02040e040850015001571857108354940e04080014005917402e6027691891749408060f0014086718600
0600067108094940d0f060204005917691e6027402861749d0060808080806080a380a080808080a0608080a0808080608080a0808b9f6e9c80808994926c808
b040207021f14110d0d0a1321080b9f684b9f6fb56f6fb56f684b6b9b459b9b4b6b94b59b94b6040405070300086285840208060100089285840307080200008
ab584040302010000838f64050608070000808b9401060504000089458600648080a48080878f9080608080a0808280608b3e3145484c4f43565a5d5164686b6
f627575757575757575757575757575757575757673707d6a6764616e5b595653505d4a4744414f3c393633303d2a2724232221202f1f1e1d1c1b1b1a1918171
716151413131211101f0f0e0d0c0b0b0a0a0a0a0a0a0a0a0a0a0909090909090909090909080808080808080808080808008f7f7f7f7f7f7f7f7f7f7f7f7f7f7
f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7e7e7d7d7c7c7b7b7a7a79797878777776767575747473737272717170707f6f6e6e6d6d6c6c6b6b6a6a6969686
8676766666565646463636262616160606f5f5f5c5a585654525f4d4b49474542404e3c3a383533313f2d2b28262422202e19890846f00882115789084fe0098
2115789084ee00a4f821159890845e0090a4f821159890844e002890a44821a0a4f82115989084dd003890a43821151190f82115989084cd00143890a4382190
a06890a41921157890846d00143890a43821157890a41921157890846d00143890a4382115489010147890a41921153890844d00143890a43821153890848000
7890a41921153890844d00143890a4382115389000106800147890a4b821153890844d00143890a43821153890847800147890a4b821153890844d00143890a4
382115389084d800147890a47821153890842d00143890a4382115389084d800147890a47821153890842d00143890a43821153890843900143890a478211538
90840d00143890a43821153890843900143890a47821153890840d00143890a43821153890845900143890a4782115389084ec00143890a43821153890845900
143890a4782115389084ec00143890a43821153890845900143890a4782115389084ec00143890a43821153890845900143890a4782115389084ec00143890a4
3821153890847900143890a4782115389084cc00143890a43821153890847900143890a47821153890dc00143890a43821153890849900143890a45821152890
ec00143890a438211538908489008038901168212890fc00143890a4382115389084290080589011982128900d00143890a43821153890840900805890119821
a028901d00143890a4382115389084a80080589011b821a058902d00143890a4382115389084880080589011b821a05890103d00143890a43821153890842800
80589011b821a05890109d00143890a438211538908480589011b821a0589010bd00143890a4382115489011b821a05890101e004890a4382115289011b821a0
5890102e005890a4c821a05890106e0080589011b821a05890102e0080589011d821a03890106e0080589011e8211538904e0080389011b821a02890a4582115
28904e00389011b821a04890a458211590843e002890117821a0589010143890a458211590842e0028907821a05890102800143890a458211590841e00289068
21a090108800143890a458211590840e001490a458211590849800143890a458211590840e001490a458211590849800143890a458211590840e001490a45821
2890a800143890a458211590840e001490a448212890b800143890a458211590840e002890a43821159084b800143890a45821159084fd003890a43821159084
b800143890a45821159084ed001438904821159084b800143890a45821159084ed001428905821159084b800143890a45821159084ed001490a458212890c800
143890a45821159084ed001490a448212890d800143890a45821159084ed002890a43821159084d800143890a45821159084dd003890a43821159084d8001438
90a45821159084cd001438904821159084d800143890a45821159084cd001428905821159084d800143890a45821159084cd001490a45821289084d800143890
a45821159084cd001490a44821389084d800143890a45821159084cd002890a43821153890e800143890a45821159084bd003890a43821152890f800143890a4
5821159084ad001438904821159084e800804890a45821159084ad001428905821155990a4582115b890840d001490a4582115499011682115b890840d001490
a4ba2115d990844b002890a4ba2115d9904b003890a45c211528904b00143890a45c211590844b0014f990a46821a04890a4d9211590844b0014f990a4582115
5890a4d9211590840d00143890a4582115289010149990a458211590840d00143890a4582115908480009990a458211590840d00143890a45821159000108900
1490a458211590840d00143890a4582115908499001490a458212890840d00143890a4582115908499001490a448213890840d00143890a45821159084990028
90a438211538901d00143890a4582115908489003890a438211528902d00143890a45821159084790014389048211590842d00143890a4582115908479001428
9058211590842d00143890a4582115908479001490a458211590842d00143890a4582115908479001490a458211590842d00143890a4582115908479001490a4
58212890842d00143890a4582115908479001490a448213890842d00143890a4582115908479002890a438211538903d00143890a4582115908469003890a438
211528904d00143890a458211590845900143890482128905d00143890a458211590845900142890482128906d00143890a4582115908459002890482128907d
00143890a4582115908449002890482128908d00143890a4582115908439001490a438211590848d00143890a4582115908439001490a438211590848d001438
90a4582115908439002890482128909d00143890a458211590842900289048212890ad00143890a458211590841900289048212890bd00143890a45821159084
0900289048212890cd00143890a45821159084f800289048212890dd00143890a45821159084e800289048212890ed00143890a45821159084d8002890482128
90fd00143890a45821159084c8002890482128900e00143890a45821159084b8001490a438211590840e00143890a45821159084b8001490a438211590840e00
143890a45821159084b8002890482128901e00143890a45821159084a8002890482128902e00143890a4582115908498002890482128903e00143890a4582115
908488002890482128904e00143890a4582115908478002890482128905e00143890a4582115908468002890482128906e00143890a458211590845800289048
212890846e00143890a458211590844800289048213890846e00143890a4582115908438001490a438211538907e00143890a4582115908438001490a4382115
28908e00143890a4582115908438002890482128909e00143890a458211590842800289048212890ae00143890a4582115908480289048212890be00143890a4
582115489048212890ce00143890a4582115389048212890de00143890a4582115289048212890ee00143890a4582115114821159084ee00143890a4b8211590
fe00143890a4b821900f00143890a4a821901f00143890a49821902f00143890a48821903f00143890a47821904f00143890a46821905f00143890a45821906f
00143890a44821907f00143890a42821a090af00145890290020222022643877275800690020722877265800890076670458008900202268000a000a000a000a
000a000a000a000a000a00190020442402b800190074287746b800f800204238776702a800f80064587724029800e8002076587767469800e800207877670288
00e800208877248800f80076787767047800f8006088772778000900747877677800090060887702680019007678770668001900204476587727680039004058
772668002002290064774728772668006246290020220064660458004076770249002022680062287706c90062287727c90072287727c90060287767c9002028
77670239002022780076776702390064660468007228770229002076772768007228770229002076776768006277670229002038770258006228772439007677
67025800722877660429007277672402480060387726290040662876674800723877263900226428770638007238772649007228774738007438770658002202
d800723877042800723877464800406646d80060387726280072487702380062287704d800762877262800624877063800622877472202b80040287726280062
48772738006238776746c800646604280042487726380040587724b800202238000074387726480074587706f80000406677660448004066487767f800280038
226800224276387702e800d80072387702e800d80062387704e800d80062387746e800d8006238776702d800d8004066387724020020229800e8002264387767
207666048800f800607877478800f80020887726026800f80020768877676800090064768877065800090020227628677648772758008002c051600010e3f3a3
a2331221029041000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
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

__sfx__
000100031b340146400e7700c070100700c070100700c070100700c070100700c070100700c070100700c070100700d070100700c070100700c070100700c070100700c070100700c070100700c070100700c070
000900001e7501e7001d7001d7001c7001b7001a70018700167001570013700117000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000500002075020750207402073020730207202071020710127001d7001d700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
000200040e3500e6500e3500e6500c350076500435001650013500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

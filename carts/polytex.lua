pico-8 cartridge // http://www.pico-8.com
version 18
__lua__
-- textured edge renderer
function polytex(v)
	local v0,nodes=v[#v],{}
	local x0,y0,w0,u0,v0=v0[1],v0[2],v0[3],v0[4],v0[5]
	for i=1,#v do
		local v1=v[i]
		local x1,y1,w1,u1,v1=v1[1],v1[2],v1[3],v1[4],v1[5]
		local _x1,_y1,_u1,_v1,_w1=x1,y1,u1,v1,w1
		if(y0>y1) x0,y0,x1,y1,w0,w1,u0,v0,u1,v1=x1,y1,x0,y0,w1,w0,u1,v1,u0,v0
		local dy=y1-y0
		local dx,dw,du,dv=(x1-x0)/dy,(w1-w0)/dy,(u1-u0)/dy,(v1-v0)/dy
		if(y0<0) x0-=y0*dx u0-=y0*du v0-=y0*dv w0-=y0*dw y0=0
		local cy0=ceil(y0)
		-- sub-pix shift
		local sy=cy0-y0
		x0+=sy*dx
		u0+=sy*du
		v0+=sy*dv
		w0+=sy*dw
		for y=cy0,min(ceil(y1)-1,127) do
			local x=nodes[y]
			if x then
				-- rectfill(x[1],y,x0,y)
				
				local a,aw,au,av,b,bw,bu,bv=x[1],x[2],x[3],x[4],x0,w0,u0,v0
				if(a>b) a,aw,au,av,b,bw,bu,bv=b,bw,bu,bv,a,aw,au,av
				local dab=b-a
				local daw,dau,dav=(bw-aw)/dab,(bu-au)/dab,(bv-av)/dab
				local ca=ceil(a)
				-- sub-pix shift
				local sa=ca-a
				au+=sa*dau
				av+=sa*dav
				aw+=sa*daw
				for k=ca,min(ceil(b)-1,127) do
					local c=sget(au/aw,av/aw)
					if(c!=11) pset(k,y,c)
					au+=dau
					av+=dav
					aw+=daw
				end
			else
				nodes[y]={x0,w0,u0,v0}
			end
			x0+=dx
			u0+=du
			v0+=dv
			w0+=dw
		end
		x0,y0,w0,u0,v0=_x1,_y1,_w1,_u1,_v1
	end
end
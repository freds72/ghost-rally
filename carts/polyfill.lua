pico-8 cartridge // http://www.pico-8.com
version 18
__lua__
-- polygon edge renderer
function polyfill(p,col)
	color(col)
	local p0,nodes=p[#p],{}
	local x0,y0=p0[1],p0[2]

	for i=1,#p do
		local p1=p[i]
		local x1,y1=p1[1],p1[2]
		-- backup before any swap
		local _x1,_y1=x1,y1
		if(y0>y1) x0,y0,x1,y1=x1,y1,x0,y0
		-- exact slope
		local dx=(x1-x0)/(y1-y0)
		if(y0<0) x0-=y0*dx y0=0
		-- subpixel shifting (after clipping)
		local cy0=ceil(y0)
		x0+=(cy0-y0)*dx
		for y=cy0,min(ceil(y1)-1,127) do
			local x=nodes[y]
			if x then
				rectfill(x,y,x0,y)
			else
				nodes[y]=x0
			end
			x0+=dx
		end
		-- next vertex
		x0,y0=_x1,_y1
	end
end
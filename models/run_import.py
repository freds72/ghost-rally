import bpy
import os

filename = os.path.join(os.path.dirname(bpy.data.filepath), "run_import.py")
exec(compile(open(filename).read(), filename, 'exec'))
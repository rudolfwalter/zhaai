from tkinter import *
from os.path import isfile
import subprocess as sp
import sys

if sys.version_info < (3, 7):
    print('Minimum required python version is 3.7')
    sys.exit(1)

ast2dot = None
if isfile('./ast2dot'):
    ast2dot = './ast2dot'
elif isfile('../ast2dot'):
    ast2dot = '../ast2dot'
else:
    print('ast2dot not found, you need to compile it')
    sys.exit(1)

if sp.run(['which','dot']).returncode != 0:
    print('graphviz dot was not found, you need to install it')
    sys.exit(1)

def regen(ev):
    global img
    print('regenerating image')

    a2d = sp.run([ast2dot], input=ast.get(), capture_output=True, encoding='utf-8')
    if a2d.returncode != 0:
        print('ast2dot failed')
        return

    with open('astdisp_temp.png', 'w') as f:
        dot = sp.run(['dot', '-Tpng'], input=a2d.stdout, encoding='utf-8', stdout=f)
        if dot.returncode != 0:
            print('graphviz dot failed')
            return

    img = PhotoImage(file='astdisp_temp.png')
    panel.configure(image=img)
    print('new image is ready')

w = Tk()
w.title('Zhaai AST visualizer')

panel = Label(w)
panel.grid(row=1, column=1)

ast = StringVar()
tb = Entry(w, textvariable=ast)
tb.grid(row=2, column=1)
tb.bind('<Return>', regen)
tb.bind('<KP_Enter>', regen)

w.mainloop()

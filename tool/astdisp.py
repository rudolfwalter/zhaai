#!/usr/bin/python3

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
    
    a2d = sp.run([ast2dot], input=ast.get(), capture_output=True, encoding='utf-8')
    if a2d.returncode != 0:
        panel.configure(image='', text='ast2dot failed')
        return

    w.update()
    panelw = panel.winfo_width()
    panelh = panel.winfo_height()
    dotsize = '-Gsize=%d,%d!' % (panelw, panelh)

    with open('astdisp_temp.png', 'w') as f:
        dot = sp.run(['dot', '-Tpng', dotsize, '-Gdpi=1'],
                     input=a2d.stdout, encoding='utf-8', stdout=f)
        if dot.returncode != 0:
            panel.configure(image='', text='graphviz dot failed')
            return

    img = PhotoImage(file='astdisp_temp.png')
    panel.configure(image=img, text='')

w = Tk()
w.geometry('300x200')
w.title('Zhaai AST visualizer')
Grid.rowconfigure(w, 0, weight=1)
Grid.columnconfigure(w, 0, weight=1)

panel = Label(w, compound=CENTER)
panel.grid(row=0, column=0, sticky=N+S+E+W)

ast = StringVar()
tb = Entry(w, textvariable=ast)
tb.grid(row=1, column=0, sticky=N+S+E+W)
tb.bind('<Return>', regen)
tb.bind('<KP_Enter>', regen)

w.mainloop()

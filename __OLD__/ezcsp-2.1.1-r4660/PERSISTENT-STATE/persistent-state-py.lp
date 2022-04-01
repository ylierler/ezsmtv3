#script(python)

import sys
import tempfile

def output_model(fname,s):
    f=open(fname, 'w')
    print >>f, s
    f.close()

def wait(pinfile):
    pin=open(pinfile,'r')
    s=pin.readline()
    pin.close()
    return s

def respond(poutfile,s):
#    print s
    pout=open(poutfile,'w')
    print >>pout,s
    pout.close()

def main(prg):
    debug=True
    pinfile="--PIPEIN--"
    poutfile="--PIPEOUT--"
    fname_model=tempfile.mktemp(".tmp","pspy-")
    output_model(fname_model,"")
    if debug: print "waiting for grounding request..."
    aspfile=wait(pinfile).strip()
    # Load ASP program specified
    if aspfile:
        prg.load(aspfile)
    prg.ground([("base", [])])
    respond(poutfile,fname_model)
    #
    if debug: print "waiting for solving request..."
    wait(pinfile)
    n=1
    with prg.solve_iter() as it:
        for m in it:
            output_model(fname_model,"Answer:"+str(n)+'\n'+str(m))
            respond(poutfile,fname_model)
            if debug: print "waiting for solving request..."
            wait(pinfile)
	    n=n+1
        switcher = {
            True: "SATISFIABLE",
            False: "UNSATISFIABLE"
        }
        output_model(fname_model,switcher.get(it.get().satisfiable, "UNKNOWN"))
        respond(poutfile,fname_model)
	#print it.get()
#end.

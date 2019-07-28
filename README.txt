
Some files can work only with coqCVS 

 They are either in subdirectories */CVSONLY  
                 or in */SRC, but compilable with make -f makeCVS all

 

        

Some files can work only with coqV8 (the official version) 

 They are either in subdirectories */V8ONLY  
                 or in */SRC, but compilable with make -f makev8 all


Other files can work indifferently with one version aor another.
use the "standard" makefile




For testing all files :

 with coqV8, "make test"

 with coqCVS, "make testCVS"



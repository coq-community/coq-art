#!/bin/bash
function parcours ()
{
for f in $1/SRC/*.v; do 
 local texname=`dirname $f`"/"`basename $f ".v" `".tex";
 if  test ! -e $texname ;then touch $texname ; fi; done
}

parcours $1

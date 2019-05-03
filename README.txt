This package provides functions to handle affine algebraic group normal basis 
for extensions over finite fields.

The package itself consists of the file "affalgpnormbasis.gp", to 
be loaded in a PARI-GP session thanks to a '\r affalgpnormbasis.gp'
GP command.  See comments at the beginning of this file to have
further details about the functions provided. 

A short examples of use, and tests, for this package are given by the
file test.gp. To launch it, simply type '\r test.gp' in a shell or use 
the 'drag and drop' method. Be sure to have the accurate path for the 
attachment of the file 'affalgpnormbasis.gp' (check it at the beginning of test.gp). 
After that you will be able to test the developed algorithms by simply 
taping the name of corresponding functions. For the Lucas torus case we 
give an 'step by step' example (with specified parameters) through the function 
'luctorusnormbasistest()'. It is worth noticing that for large finite field we have 
to manage the stack size. 
 


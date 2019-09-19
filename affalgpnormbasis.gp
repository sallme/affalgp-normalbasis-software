/***
 *  Title: Normal Basis for Finite Fields using 1-dimensional algebraic groups
 *	
 */
 
 /***
 *
 * This file provides GP 'routines' to handle bases (with low complexity) 
 * for extensions (of degree d) of finite fields (with q elements) such that there
 * exists fast algorithms to compute Frobenius, and multiplications.
 * Developed in [EzSa2018], these basis make use of affine algebraic groups 
 * of dimension 1. They are available for different degrees extension
 * and they are constructed from the method described in [CoLe2009].
 * It is worth to add that this code proposes 
 * three basis, two of them with low complexity, and each one of them 
 * provides fast multiplication in the considered finite field. Since
 * they are normal basis the Frobenius can be computed efficiently.
 * Further we give auxiliary fonctions which are relevant in the sequel.
 * Specially in the Lucas torus case, we implement a number of functions
 * in order to manage the group law structure.
 
 * More precisely, given a GP finite field Fq, with q elements, a
 * call to the functions 'addgroupnormbasis', 'multgroupnormbasis', and
 * 'luctorusnormbasis', return normal basis. When everything is 
 * ok, the field 'Fqd' contains a GP degree d extension defined by a polynomial
 * basis. If necessary, we take advantage of the algebraic groups properties
 * to give our own irreducible polynomials using the functions
 * schreierFindIrreduciblePolynomial, kummerFindIrreduciblePolynomial, and
 * lucasFindIrreduciblePolynomial. Thus elements in Fqd ares given by 
 * polynomials.
 
 * Calls to 'convertFromPolynomialBasisToNormalBasis' sends an element, given 
 * in the polynomial basis, into a normal basis. Elements in these 
 * basis are then given by elements of a vector space of dimension
 * d over Fq. Conversely, given a vector in the normal basis
 * 'convertFromNormalBasisToPolynomialBasis' gives its polynomial
 * representation.
 
 * In any basis, additions/substraction are performed through the '+/-' GP
 * operation. Routines for multiplications, and Frobenius are provided 
 * as well but depend on the basis. In the polynomial representation, 
 * we handle these operations through the usual GP syntax. In the normal 
 * basis, we provide for this task the functions 'addgroupnormbasisfastmult',
 * 'multgroupnormbasisfastprod', and 'luctorusnormbasisfastmult'.
   
 * For each one of the basis we give practical examples (see test.gp). 
 * In the functions's code, we have some tests, that are commented.
 *
 */
 
 
 /***
 * Warning: These functions are written using PARI/GP 2.12.0. If you 
 * are still using some earlier versions, then you may going to run into 
 * problems because you may not have some functions like ffmaprel, ffextend, 
 * or ffembed.
 *
 *
 * See end of file for bibliography.
 */
 
 
 
/*****************************************************************************************************************************
******************************************************************************************************************************
******************************************************************************************************************************
**********                                       Some Auxiliary Functions                                           **********
******************************************************************************************************************************
******************************************************************************************************************************
Auxiliary Functions Related to Vectors                                                                              **********
Auxiliary Functions Related to Basis and Matrices                                                                   **********
*****************************************************************************************************************************/
/* Variable priorities */
     'x; 'y; 'z; 'r;
	 
	 
/********************************************************
                                              Auxiliary Functions Related to Vectors 
                                                             *****************************************************************/

/* Convolutional Product, same as fastConvolutionalProduct but slower */
AlgConvolutionalProduct(A, B)=
{
   if(length(A) != length(B), return("Impossible operation"));
   my(d=length(A), V=vector(d));

      for(j=0, d-1,
                   for(i=0, d-1, V[j+1]+=A[i+1]*B[1+((j-i)% d)]);
         );

   return(V);
}

/* Convolutional product, same as AlgConvolutionalProduct but faster.
  We take adavantage of GP's implementation of polynomial products
  to get a not too slow convolution product.
*/
 fastConvolutionalProduct(A, B) =
 {
     if(length(A) != length(B), return("Impossible operation"));
     my(d=length(A), Cp=vector(d), pC);

        pC =  Polrev(A)*Polrev(B);
        for(i=0, d-1, Cp[i+1] = polcoef(pC, i));
        for(i=d, 2*d-1, Cp[i+1-d]+ = polcoef(pC, i));
        
            /* Testing if it fits AlgConvolutionalProduct, OK it works */
               \\print(Cp == AlgConvolutionalProduct(A, B));
        
     return(Cp);
 }	


/* Inverse Convolutional Product */
invConvolutionalProduct(A) =
{
		 
    my(d=length(A), V=vector(d));
    my(Pvx = Polrev(A));

       ax = lift(Mod(Pvx, 'x^d-1)^-1);
       V = Vecrev(ax, d);

       		 /* Testing inverse, it works unless the polynomial is not inversible !!! */
                    \\fastConvolutionalProduct(A, V));

     return(V);
} 


/* Dot product */
AlgDotProduct(A, B) =
{
    my(d = length(A), C = vector(d));
	
       if(length(B) != d, return("Impossible operation"));
       for(j = 0, d-1, C[1+j] = A[1+j]*B[1+j]);
   
    return(C);
}

/* Circular shift */
AlgSigma(A) = 
{
    my(d = length(A), C = vector(d));

        for(j = 0, d-1, C[1+j] = A[1+((j-1) % d)]);

    return(C);
}


/********************************************************
                                        Auxiliary Functions Related to Basis and Matrices
                                                             ***************************************************************/


/* Given a in Fq^d return the relative trace of a */															 
relativetrace(a, d) =
{
    if(a.f == d, return(trace(a)));
    my(p=a.p, q=p^(a.f / d), rtra=a);
	my(Fq = ffgen(q, 'r), mFqd, imFqd, rtraCoerced);

          for(i=1, d-1, rtra = rtra + a^(q^i));
          
          /* Sending the trace in the base field Fq, Ok it works */
		     mFqd        = ffembed(Fq, a);
			 imFqd       = ffinvmap(mFqd);			 
             rtraCoerced = ffmap(imFqd, rtra);

    return(rtraCoerced);
}


/* Test if a vector B form a basis */
isbasis(B)=
{
    my(d=length(B), MBD, test = 0);
	
       MBD = Mat(vector(d,i, Colrev(B[i].pol)));
       if(matdet(MBD) != 0, test=1);

    return(test);
}


/* Test whether a given element in Fq^d/Fq is a normal element */
isnormal(NElt, d) =
{
    my(p = NElt.p, q=(p^((NElt.f) / d)));
    my(ENB  = vector(d), Frobx, tgcd);

         for(i=0, d-1, ENB[i+1] = NElt^(q^i));
         Frobx = Polrev(ENB);
         tgcd = gcd(Frobx, 'x^d-1);

    return(poldegree(tgcd) == 0);
}
														 


/* Normal Basis Representation: 
   Note: it works only with prime base field i.e, Fq/Fp 
*/
convertFromPolynomialToNBasis(x, B)=
{
	my(p=x.p, d=length(B), Fp = ffgen(p));	
	if(x.f != d, return("This function works only with prime base field."));
	my(MPass = matrix(d, d), PBcoorx, NBcoorx);
	
	    /* Determination of the passage matrix */	   
	    for(i=1, d,
		          for(j=1, d, MPass[i, j] = (Vecrev(B[i].pol, d)[j])*Fp^0);
	       );
	    MPass = mattranspose(MPass); 
	    /* Representation of x in the normal basis B */
        PBcoorx = (Vecrev(x.pol, d))*Fp^0;
	    NBcoorx = matinverseimage(MPass, PBcoorx~);
                     
	return(lift(NBcoorx~));
}


/* Relative representation of an x in Fq^d over Fq */
representInExtendedPolBasis(x, Fq)=
{
	my(p = x.p, q = p^(Fq.f), mFqd); 

        mFqd = ffembed(Fq, x);
		imFqd = ffinvmap(mFqd);
        xd = ffmaprel(imFqd, x);
		 
	return(lift(xd));
}

VecrepresentInExtendedPolBasis(V, Fq)=
{
     my(d = length(V), Vd = vector(d));
	 
	     for(i=1, d, Vd[i] = representInExtendedPolBasis(V[i], Fq));
	
	return(Vd);
}

/* Extended version of convertFromPolynomialToNBasis */
convertFromPolynomialToNBasisExtended(x, B)=
{
	my(p=x.p, d=length(B), q=p^(x.f / d));
    my(Fq = ffgen(q, 'r));		
	my(MPass = matrix(d, d), PBcoorx, NBcoorx);
	   
	   /* Determination of the passage matrix */	   
	   for(i=1, d,
		          for(j=1, d, MPass[i, j] = (Vecrev(representInExtendedPolBasis(B[i], Fq), d)[j]));
	       );
	   MPass = mattranspose(MPass); 

	   /* Then one gives, the representation of x in the NB */
        PBcoorx = Vecrev(representInExtendedPolBasis(x, Fq), d);
	    NBcoorx = matinverseimage(MPass, PBcoorx~);  
                     

	return(lift(NBcoorx~));
}


/* Given x, return the normal basis representation of x */
convertFromPolynomialBasisToNormalBasis(x, B)=
{
	my(d = length(B));
	
	     if(x.f == d, return(convertFromPolynomialToNBasis(x, B)));
		 
	return(convertFromPolynomialToNBasisExtended(x, B));
}


/* Given x in a normal basis B, return polynomial representation of x */
convertFromNormalBasisToPolynomialBasis(x, B)=
{
	my(d = length(B), xp = 0);
	 
	     for(i=1, d, xp+ = x[i]*B[i]);	
		 
	return(xp); 
}


/* Return the complexity of a normal basis. */
normalBasisWeight(B) = 
{
	 my(d = length(B), Nelt = B[1], Mnb, wB=0);
	 
	     Mnb = vector(d,i, convertFromPolynomialBasisToNormalBasis(Nelt*B[i], B));
		 for(i=1, d,
					for(j=1, d, 
					           if(Mnb[i][j] != 0, wB+ = 1);
					    )
			 );

     return(wB);
}



/****************************************************************************************************************************
*****************************************************************************************************************************
*****************************************************************************************************************************
**********                                Normal Basis using additive group (Artin-schreier theory)                   *******
*****************************************************************************************************************************
*****************************************************************************************************************************
Implemented Functions                                                                                              **********
    schreierFindIrreduciblePolynomial(Fq, d)  ---> return a degree d irreducible polynomial over Fq                **********
    addgroupnormbasis(Fq, d)                  ---> return a normal basis of Fq^d/Fq, with good properties          **********
    addgroupnormbasisfastmult(A, B, artB)     ---> perform fast multiplication in Fq^d                             **********
****************************************************************************************************************************/


/* Construction of a irreducible polynomial through Artin-Schreier theory.
   Reference: [CoLe2013] 
*/
schreierFindIrreduciblePolynomial(Fq, d) =
{
    my(p = Fq.p, q = p^(Fq.f), a, Px);
    
         Nx = 'x^p-1;
         Dx = 'x;
         for(i=2, p-1,
                         Dx+ = 'x^i;
             );
         Ix = Nx \ Dx;
         a = ffprimroot(Fq);
         while(trace(a)==0 || trace(a^-1)==0, a=ffprimroot(Fq););
         Px = 'x^p-'x-a;

    return (Px);
}



/* Return a normal basis with low complexity (sub-quadratic bounds),
   and allowing fast mutiplication (quasi-linear time) in Fq^d.
   Reference: [EzSa2018]
 */
addgroupnormbasis(Fq, d) =  
{
     my(p = Fq.p, q = p^(Fq.f));
	 my(Px, artB = vector(d));

         if(d != p, return("Impossible to construct this normal basis"));
		 until(polisirreducible(Px), Px = schreierFindIrreduciblePolynomial(Fq, d));
         [b, mFqd] = ffextend(Fq, Px, 'r);
         /* Determination of the normal element */
             Nelt = 1/b;
             artB[1] = Nelt;
             for(j=1, d-1, artB[j+1] = 1 / (b - j));
			 
			         /* Testing if Nelt is normal, Ok it works */
					     \\print(isnormal(Nelt, d));
					 /* Testing the complexity of the normal basis, Ok it works */
                         \\print("The complexity must be less or equal to 3*p-2=" 3*p-2);						 
                         \\print("We found the following complexity: " normalBasisWeight(artB));							 

     return(artB);
}


/*************************** Fast multiplication using Artin schreier Normal Basis ********************************/

/* Perform a fast multiplication (quasi-linear time) of 
   two elements A, and B in the normal basis of Fq^d over Fq. 
   Reference: [EzSa2018]
 */
addgroupnormbasisfastmult(A, B, artB) = 
{  	
	my(d = length(artB));
	if(!isnormal(artB[1], d), 
	       return("Sorry none additive normal basis exist")
	   );
	my(p = A.p, q = p^(A.f / d), Fp = ffgen(p), Fq = ffgen(q, 'r));
		
		
		
	my(Nelt = artB[1], b=1/Nelt);
	my(mFq = ffembed(Fp, Fq), mFqd = ffembed(Fq, Nelt), imFq = ffinvmap(mFq));	
	my(Zi0, Iota, t, R, Ur, Wr, AB, ABtest, Atest);
                      
        /* Multiplication Parameters */
		    Zi0  = Nelt^2;
			Iota = convertFromPolynomialBasisToNormalBasis(Zi0, artB);
			     
			    /* Determination of t=Frobenius(b)-b and R outside of <t> */
				     t = 1;
					 until(R != 0 && R != t, R = random(Fq));
		
        /* To avoid 'inconsistent multiplication t_FFELT * t_FFELT', we send parameters in Fq^d */		
			t = ffmap(mFq, t);
			Ur = vector(d);			      
			      for(i=1, d, Ur[i] = 1/(R+(i-1)*t));
			Uri = invConvolutionalProduct(Ur);         			 
            Wr = vector(d, i, (1/(R+(i-1)*t))^2);
			
		/* Representation in the normal basis */
		    print("\e[1;34mRepresentation in the normal basis\e[0m");
			print("The two elements to multiply are:");
			print("A = " A);
			print("B = " B);
			alph = convertFromPolynomialBasisToNormalBasis(A, artB);
            beta = convertFromPolynomialBasisToNormalBasis(B, artB);
            print("Coordinate of A in the polynomial basis : ");
			print(Vecrev(representInExtendedPolBasis(A, Fq), d));
            print("Coordinate of A in the normal basis: ");
			print(alph);
                    /* Testing if the coordinates fit */
					   Atest = 0;
                       for(i=1, d, Atest+ = ffmap(mFqd, alph[i])*artB[i]);
                       \\print("The element A = "Atest);
                       print("Do the two coordinates represente the same element A? (1=yes and 0=no) "A == Atest);
			print("Note: It should be the same case for the second element B");
			
		/* Multiplication of A and B in the normal basis */
            print("\e[1;34mMultiplication of the two elements in the normal basis\e[0m");		
			AB = fastConvolutionalProduct(Iota, AlgDotProduct(alph, beta)) +
            fastConvolutionalProduct(Uri, AlgDotProduct(fastConvolutionalProduct(Ur, alph), fastConvolutionalProduct(Ur, beta))
                                        -fastConvolutionalProduct(Wr,  AlgDotProduct(alph, beta)));									
			
			print("Their product in the normal basis is:");
			print(AB);
	
}


/****************************************************************************************************************************
*****************************************************************************************************************************
*****************************************************************************************************************************
**********                                  Normal Basis using multiplicative group (Kummer Theory)                   *******
*****************************************************************************************************************************
Implemented Functions                                                                                             ***********  
    kummerFindIrreduciblePolynomial(Fq, d)      ---> return a degree d irreducible polynomial over Fq             ***********
    multgroupnormbasis(Fq, d)                   ---> return a normal basis of Fq^d over Fq with good properties   ***********
    multgroupnormbasisfastprod(A, B, kumB)      ---> fast multiplication of two elements A, and B in Fq^d     	  ***********
****************************************************************************************************************************/


/* Construction Of a irreducible polynomial through Kummer theory
   Reference: [CoLe2013]
 */
kummerFindIrreduciblePolynomial(Fq, d) =
{
    my(p = Fq.p, q = p^(Fq.f), l, n);
	my(e, m, r=0, a=0, test);    

	    [l, n] = factor(d)[1, ];     
               if((q-1) % l != 0, 
	                  return("Impossible to find irreducible polynomial through Kummer theory");
                  );

      /* Generator a of the l-Sylow */         
         for(i=1, omega(q-1), [test, e]=factor(q-1)[i, ]; if(test==l, break));
         m = (q-1) / (l^(e));         
             until(a^(l^(e-1)) != 1 && r != 0, r=random(Fq); a=r^m); 
        Px = 'x^d-a;
		
		         /* Test of irreducibility, Ok it works */
				    \\ print(polisirreducible(Px));

    return(Px);
}


/* Return a normal basis with low complexity (sub-quadratic bounds),
   and allowing fast mutiplication (quasi-linear time) in Fq^d. 
   Reference: [EzSa2018]
*/
multgroupnormbasis(Fq, d) =  
{
    my(p  = Fq.p, q = p^(Fq.f));
	if(gcd(p, d) != 1 || (q-1)%d !=0, 
	                 return("Impossible to construct this normal basis");
            );
	my(Px, a, b, mFqd);
	my(Nelt, zi, kumB);         

         /* Kummer Irreducible polynomial */
            Px = kummerFindIrreduciblePolynomial(Fq, d); 
                if(type(Px)=="t_STR", return(Px));
            a  = -polcoeff(Px, 0);

                      /* Taking advantage of Pari Functions */
                         if( !polisirreducible(Px),
                                 a  = ffprimroot(Fq);
                                 Px = 'x^d-a
                           );
        [b, mFqd] = ffextend(Fq, Px, 'r);
    
    
        /* definition of the normal basis */
         Nelt = 1/(b-1);
	     zi   = polrootsmod('x^d-1, b)[2]; 
         kumB = vector(d); kumB[1] = Nelt;
                for(i=1, d-1, kumB[i+1] = 1/((zi^i)*b-1));
			 
			         /* Testing if the basis is normal, Ok it works */
                         \\print(isnormal(Nelt, d)); 

    return(kumB);
}


/* Fast multiplication using mutiplicative normal basis 
   Reference: [EzSa2018]
*/
multgroupnormbasisfastprod(A, B, kumB) = 
{
	my(d = length(kumB));
	if(!isnormal(kumB[1], d), 
	       return("Sorry none multiplicative normal basis exist")
	   );
	my(p = A.p, q = p^(A.f / d), Fq = ffgen(q, 'r)); 
		 
	/* We have to recover some parameters from the basis */
	my(Nelt = kumB[1], b = 1+(1/Nelt));
	my(zi = ((1/kumB[2])+1)/b);
	my(mFqd = ffembed(Fq, Nelt), imFqd = ffinvmap(mFqd));  
	my(Zi0, Iota, t, R, Ur, Uri, Wr);
	my(AB, ABtest, Atest);
	
	     /* Multiplication Parameters */
		     Zi0  = kumB[1]^2;
			 Iota = convertFromPolynomialBasisToNormalBasis(Zi0, kumB);
			 /* Determination of t, and R: [EzSa2018, 3.1 & 3.2] */
				 t = ffmap(imFqd, zi);
			     R = random(Fq);
					while(R^d == 1 || R == 0 || (1-R)^d == 1, R = random(Fq));
						
						    /* testing if the order of t is d, Ok it works */
							   \\print(fforder(t));
							   
		    Ur = vector(d);			      
			     for(i=1, d, Ur[i] = 1/(R+t^(i-1)-1));
		    Uri = invConvolutionalProduct(Ur); 
		             /* Testing inverse, it works unless the polynomial is not inversible !!! */
                        \\print("Inverse convolutional product test:" fastConvolutionalProduct(Ur, Uri));						
            Wr = vector(d, i, (1/(R+t^(i-1)-1))^2);
			
		/* Representation in the normal basis */
		    print("\e[1;34mRepresentation in the normal basis\e[0m");
			print("The two elements to multiply are:");
			print("A = " A);
			print("B = " B);
			alph = convertFromPolynomialBasisToNormalBasis(A, kumB);
            beta = convertFromPolynomialBasisToNormalBasis(B, kumB);
            print("Coordinate of A in the polynomial basis : ");
			print(Vecrev(representInExtendedPolBasis(A, Fq), d));
            print("Coordinate of A in the normal basis: ");
			print(alph);
                    /* Testing if the coordinates fit */
					   Atest = 0;
                       for(i=1, d, Atest+ = ffmap(mFqd, alph[i])*kumB[i]);
                       print("Do the two coordinates represente the same element A? (1=yes and 0=no) "A == Atest);
			print("Note: It should be the same case for the second element B");
			
		/* Multiplication of A and B in the normal basis */
            print("\e[1;34mMultiplication of the two elements in the normal basis\e[0m");		
			AB = fastConvolutionalProduct(Iota, AlgDotProduct(alph, beta)) +
            fastConvolutionalProduct(Uri, AlgDotProduct(fastConvolutionalProduct(Ur, alph), fastConvolutionalProduct(Ur, beta))
                                        -fastConvolutionalProduct(Wr,  AlgDotProduct(alph, beta)));
			print("Their product in the normal basis is:");
			print(AB);
}




/****************************************************************************************************************************
*****************************************************************************************************************************
*****************************************************************************************************************************
**********                                        Normal Basis using Lucas torus                                      *******
*****************************************************************************************************************************
*****************************************************************************************************************************
Implemented Functions                                                                                             ***********
    numerous auxiliary functions                                                                                  ***********
	lucasFindIrreduciblePolynomial(Fq, d)     ---> return a degree d irreducible polynomial over Fq               ***********
    luctorusnormbasis(TD, d)                  ---> return a normal basis of Fq^d over Fq, b st Fq^d=Fq(b), and t  ***********
    luctorusnormbasisfastmult(A, B, TD)       ---> fast multiplication of two elements A, and B in Fq^d           ***********
****************************************************************************************************************************/


/********************************* Definition of an appropriate torus *************************************/

/* Return a Lucas torus with specific parameters.
   Note: d divides q+1 
*/
lucasFindTorus(Fq, d) =
{
   my(p = Fq.p, q = p^(Fq.f));
   if ((q+1) % d != 0 || p == 2, return("Impossible to find a Lucas torus"));
   my(D);

         until(!issquare(D), D = random(Fq));
         \\print("We work with the Lucas torus over GF(" q") defined by D = "D);

   return(D);
}


lucasParameters(D)=
{
     my(PDx, rD, mD, imD);

         PDx = x^2-D;
         [rD, mD]= ffextend(D, PDx, 'r);
         imD = ffinvmap(mD);

     return([D, rD, mD, imD]);
}
			 

/* Given Lucas torus parameters return a point on the curve.
   Same as lucaRandomPara, but slower.
 */			 
lucasRandom(TD) = 
{
    my(D = TD[1], x1, Ty, STy, test = 0);

    while(test==0,
                  x1  = random(D);
                  Ty  = x1^2-D*'y^2-1;
                  STy = polrootsmod(Ty);
                      if(length(STy) != 0, y1=STy[1]; test = 1);
         );

    return([x1, y1]);
}			 

/*Given Lucas torus parameters return a point on the curve
  Same as lucaRandomPara, but can be slower 
 */			 
lucasRandomTwist(TD) =
{
      my(rD = TD[2], z);
         until(norm(z) == 1, z = random(rD));
      return(lucasTordueQuadratiqueInv(TD, z));
}

/*Given Lucas torus parameters return a point on the curve 
  Take advantage from the parametrisation */
lucasRandomPara(TD) =
{
    my(D = TD[1], t);
         t = random(D);
    return([(t^2+D)/(t^2-D), (2*t)/(t^2-D)]);
}	


lucasTordueQuadratique(TD, A) =
{
     my([D, rD, mD, imD] = TD);
     my(AD1, AD2);

        [AD1, AD2] = ffmap(mD, A);

     return(AD1+rD*AD2);
}

lucasTordueQuadratiqueInv(TD, z) =
{
     my(imD = TD[4], rD = TD[2]);

        if(norm(z) != 1, return("the chosen element is not on the torus"));

     return(ffmap(imD,[(z^2+1) / (2*z), (z^2-1) / (2*z*rD)]));
}	


lucasIsonCurve(TD, A) =
{
    my(D = TD[1]);
    my([x1, y1] = A);

       return(x1^2-D*y1^2 == 1);
}

lucasIsonCurveTwist(TD, A) =
{
    my(D = TD[1]);
    my(p=D.p, q=p^(D.f), z);

    z = lucasTordueQuadratique(TD, A);
        if([A[1]^(q-1), A[2]^(q-1)] != [1, 1] || norm(z) != 1, return(0));

    return(1);
}

lucasAddTwist(TD, A, B)=
{
   my(a, b);

      if(!lucasIsonCurve(TD, A) || !lucasIsonCurve(TD, B), return("Impossible operation"));

         a = lucasTordueQuadratique(TD, A);
         b = lucasTordueQuadratique(TD, B);

   return (a*b);
}

/********************************** Definition of functions for the group law **********************************/

lucasAdd(TD, A, B)=
{
   my(D = TD[1]);
   my([x1, y1] = A, [x2, y2] = B);

      if(!lucasIsonCurve(TD, A) || !lucasIsonCurve(TD, B), return("Impossible operation"));

   return ([x1*x2 + D*y1*y2, x1*y2 + x2*y1]);
}

lucasDouble(TD, A) =
{
    my([x1, y1] = A, D = TD[1]);

       if(!lucasIsonCurve(TD, A), return("Impossible operation"));

    return([x1^2+D*y1^2, 2*x1*y1]);
}


lucasExponentiation(TD, A, k) =
{
    my(kb = binary(k), kA = A);

         if(k<0 || !lucasIsonCurve(TD, A), return("Impossible operation"),
             k == 1, return(A),
             k == 0, return ([1, 0])
           );

         for(i = 2, length(kb),
                          kA = lucasDouble(TD, kA);
                          if(kb[i]==1, kA = lucasAdd(TD, kA, A));
            );

    return(kA);
}

lucasExponentiationTwist(TD, A, k) =
{
    if( k<0 || !lucasIsonCurve(TD, A), return("Impossible operation"),
        k == 0, return (1),
       );
    my(a=lucasTordueQuadratique(TD, A));
	
    return(a^k);
}


lucasMinus(TD, A)=
{
   my([x1, y1] = A);

      if(!lucasIsonCurve(TD, A), return("Impossible operation"));

   return([x1, -y1]);
}

lucasSubs(TD, A, B) = lucasAdd(TD, A, lucasMinus(TD, B));


lucasOrderTwist(TD, A) =
{
   my(a);

      if(
          !lucasIsonCurve(TD, A), return("Impossible operation"),
          A == [1, 0], return(1)
        );
      a=lucasTordueQuadratique(TD, A);

   return(fforder(a)); 
}


lucasOrder(TD, P) =
{
  my(k=2, kP=P);

     if(
          !lucasIsonCurve(TD, P), return("Impossible operation"),
          P == [1, 0], return(1)
        );
     while(kP != [1, 0],
                 kP = lucasExponentiation(TD, P, k);
                 k  = k+1;
          );

  return(k-1);
}
/* testing if the two functions are equal, OK it works. The fastest is the Twist
   for(i=1, 10, A = lucasRandomPara(TD); print(lucasOrder(TD, A) == lucasOrderTwist(TD, A))) */


lucasPointsOfPrescribedOrder(TD, d) =
{
   my(D = TD[1], rD = TD[2]);
   my(p  = rD.p, q = p^(D.f), card = q+1);
   my(P);

      if(card % d != 0, return("Impossible to generate this point"));

      until(lucasOrderTwist(TD, P) == d, P = lucasRandomPara(TD));

   return(P);
}


/* Construction Of an irreducible polynomial through Lucas torus */
lucasFindIrreduciblePolynomial(TD, n) =
{
    my(D = TD[1]);
    my(p  = D.p, q = p^(D.f), card = q+1);
    my(Nx, Dx, a, Ua, Ixa);

         Nx = D^0*('x^n);
         forstep(l=2, n, 2,
                             Nx = Nx + binomial(n, l)*(D^(l / 2))*'x^(n-l);
                );
         Dx = D^0*(n*D*'x^(n-1));
         forstep(l=3, n, 2,
                             Dx = Dx + binomial(n, l)*(D^((l-1) / 2))*'x^(n-l);
                );

         a    = lucasPointsOfPrescribedOrder(TD, card);
         Ua   = a[1]/a[2];
         Ixa  = Nx-Ua*Dx;

    return([Ixa, a]);
}



lucasParametersExtend(TD, n)=
{
     my(D = TD[1]);
     my(Px, rFqd, mFqd, imFqd, GTq, test=0);
     my(Dd);

     until(polisirreducible(Px),
                               [Px, GTq] = lucasFindIrreduciblePolynomial(TD, n)

           );

     [rFqd, mFqd] = ffextend(D, Px, 'r);
     imFqd = ffinvmap(mFqd);
     Dd = ffmap(mFqd, D);

     return([Dd, rFqd, mFqd, imFqd, GTq]);
}
 

/* Return a point defined in the extended field */		 
lucasPoint(TD, TDd) =
{
    my(D = TD[1],  mFqd = TDd[3]);
    my(p=D.p, q=p^(D.f),  test=0);
    my(Dd, x1, y1);
    Dd  = ffmap(mFqd, D);
    until(test != 0, \\ && (y1^(q-1)!=1 || x1^(q-1)!=1),
               t = random(Dd);
               [x1, y1] = [(t^2+Dd)/(t^2-Dd), (2*t)/(t^2-Dd)];
                   if(y1^(q-1)!=1 || x1^(q-1)!=1, test = 1);
         );

                   /* Testing Ok it works */
                       /*print(lucasIsonCurve(TDd, [x1, y1]));*/

   return([x1, y1]);
}
		 


/***** Definition of functions for normal basis construction. The reference is [EzSa2018] ***********/

lucasUot(TD, t, P) =
{
   my(x1, y1, xP, yP);

      if(t == [1, 0] || P == [1, 0] || t == P,
                    return("Impossible operation");
         );
      [x1, y1] = t;
      [xP, yP] = P;

   return (1 +(1/(yP-(y1*(xP-1)/(x1-1)))));
}

lucasUkt(TD, t, k, P) =
{
   kt = lucasExponentiation(TD, t, k);
   return(lucasUot(TD, t, lucasSubs(TD, P, kt)));
}


lucasFindFiberElementTwist(TD, n, A) =
{
    my(a, b, B);

       a = lucasTordueQuadratique(TD, A);
       iferr(
              b=sqrtn(a, n); B = lucasTordueQuadratiqueInv(TD, b); return(B),
              E,
              return("Impossible operation : there is no n-th root")
            );

}


lucasFindFiberElement(TD, d, a) =
{
    my(D = TD[1], TDd = lucasParametersExtend(TD, d),  mFqd = TDd[3]);
    my([x1, y1] = ffmap(mFqd, a), Dd = ffmap(mFqd, D), b1, b2);

    Nx = Dd^0*('x^d);
    forstep(l=2, d, 2,
                      Nx = Nx + binomial(d, l)*(('x^2-1)^(l / 2))*'x^(d-l);
           );
    Dx = Dd^0*(d*'x^(d-1));
    forstep(l=3, d, 2,
                      Dx = Dx + binomial(d, l)*(('x^2-1)^((l-1) / 2))*'x^(d-l);
           );

    b1 = polrootsmod(Dd^0*(Nx-x1))[1];
    b2 = y1 / subst(Dx, 'x, b1);

                              /* Testing, OK it works */
                               \\ print(lucasIsonCurve(TDd, [b1, b2]));
                               \\ print([Nx, Dx]);

    return([b1, b2]);
}




/*********************************************** Construction of the Normal Basis ******************************************/

/* Return a normal basis allowing fast mutiplication 
   (quasi-linear time) in Fq^d. 
   Reference: [EzSa2018]
*/
luctorusnormbasis(TD, d) = 
{
   my([D, rD, mD, imD] = TD);
   my(TDd = lucasParametersExtend(TD, d), [Dd, rFqd, mFqd, imFqd, GTq] = TDd);
   my(p=D.p, q=(p^(D.f)));
   my(cstc, csta, cstb, cstad, cstbd, Nelt);


        /* Determination of preimage, b, of a generator, GTq, of TDq quotiented
           b = lucasPoint(TD, TDd);
           while(lucasExponentiation(TDd, b, d) == [1, 0],
                  b = lucasPoint(TD, TDd);
                );
		   This may be slow for large q, so we use the function lucasFindFiberElement.
        */

                /*  Searching b by taking advantage of lucasFindFiberElement */
                    b = lucasFindFiberElement(TD, d, GTq);
					
		/* Generator of the d-torsion
                 t = lucasPointsOfPrescribedOrder(TD, d);              
		   deprecated,  because it may be slow	         */

         /* Generator of the the d-torsion, by taking advantage of the group structure */
           Gg = lucasSubs(TDd, [b[1]^q, b[2]^q], b);
           t = ffmap(imFqd, Gg);
                   /* testing if the point t is of order d, OK it works */
                      \\ print(lucasOrderTwist(TD, t) == d);
             

        /* determination of the constants */
           until(lucasExponentiation(TD, bt, d) != [1, 0], bt = lucasRandomPara(TD));
           cstc = lucasUot(TD, t, bt);
           for(k=1, d-1, cstc = cstc + lucasUkt(TD, t, k, bt));

                   /* Testing if the constancy held, OK it works */
                      \\ cstcd = lucasUot(TDd, ffmap(mFqd, t), b);
                      \\ for(k=1, d-1, cstcd = cstcd + lucasUkt(TDd, ffmap(mFqd, t), k, b));
                      \\ print([cstc, cstcd]);

           if(cstc == 0,
                       csta = D^0; cstb = D^0 / d,
              csta = 1 / cstc; cstb = D^0*0
             );
		/* To avoid inconsistent multiplication t_FFELT * t_FFELT, we send constants in Fq^d */
		    [cstad, cstbd] = ffmap(mFqd, [csta, cstb]);

			 
        /* Construction of the normal element */     
           Nelt = cstad*lucasUot(TDd, ffmap(mFqd, t), b) + cstbd;
           LucB = vector(d); LucB[1] = Nelt;
              for(k=1, d-1,
                      LucB[k+1] = cstad*lucasUkt(TDd, ffmap(mFqd, t), k, b) + cstbd
                  );

                    /* Testing if the basis fits with the conjugates of Nelt, OK it works */
                       \\LucBtest = vector(d);
                       \\for(k=0, d-1,
                       \\        LucBtest[k+1] = Nelt^(q^k);
                       \\   );

    return([LucB, b, t, csta, cstb]);
}




/********************* Fast multiplication using Lucas Torus Normal Basis **********************/

/* Perform fast multiplication using Lucas torus normal basis. 
   Reference: [EzSa2018]
*/
luctorusnormbasisfastmult(A, B, TD) = 
{
	my(p = A.p, D = TD[1], d = (A.f)/D.f);
	my([lucB, b, t, csta, cstb] = luctorusnormbasis(TD, d), Nelt = lucB[1]);
    my(alph, beta);
    my(v0b, Zi0, Iota, R, Ur, Wr, Uri, Sigmax, Sigmay, AB);
	
	    /* Multiplication Parameters */
	    v0b   = (b[1]-1)/b[2];
        Zi0   = 1 / v0b^2;
        Iota = convertFromPolynomialBasisToNormalBasis(Zi0, lucB);
        until(lucasExponentiation(TD, R, d) != [1, 0], R = lucasRandomPara(TD));
		
		Ur = vector(d);
        Wr = vector(d);
            for(i=1, d,
                      P     = lucasAdd(TD, R, lucasExponentiation(TD, t, i-1));
                      Ur[i] = csta*lucasUot(TD, t, P) + cstb;
                      v0    = (P[1]-1) / P[2];
                      Wr[i] = 1 / v0^2;
                );       
        Uri = invConvolutionalProduct(Ur);
				   
		print("\e[1;34mWe work with the following multiplication parameters:\e[0m ");
		print("v0   = "v0b); print("Zi0  = "Zi0); print("Iota = "Iota); 
		print("Ur   = "Ur); print("Wr   = "Wr);
				   
		Iota   = ((D^2)/4)*Iota;
        Wr     = ((D^2)/4)*Wr;        

		print("\e[1;34mRepresentation in the normal basis\e[0m");
		print("The two elements to multiply are:");
		print("A = " A);
		print("B = " B);
		alph = convertFromPolynomialBasisToNormalBasis(A, lucB);
        beta = convertFromPolynomialBasisToNormalBasis(B, lucB);
        print("Coordinate of A in the polynomial basis : ");
	    print(Vecrev(representInExtendedPolBasis(A, D), d));
        print("Coordinate of A in the normal basis: ");
	    print(alph);
                    /* Testing if the coordinates fit, Ok it works */
					   Atest = 0;
					   my(mFqd = ffembed(D, A));
                       for(i=1, d, Atest+ = ffmap(mFqd, alph[i])*lucB[i]);
                       print("Do the two coordinates represente the same element A? (1=yes and 0=no) "A == Atest);
		print("Note: It should be the same case for the second element B");	
		
		Sigmax = AlgSigma(alph);
        Sigmay = AlgSigma(beta);
        print("\e[1;34mMultiplication of the two elements in the normal basis\e[0m");		
        AB = fastConvolutionalProduct(Iota, AlgDotProduct(alph-Sigmax, beta-Sigmay)) +
                 fastConvolutionalProduct(Uri, AlgDotProduct(fastConvolutionalProduct(Ur, alph), fastConvolutionalProduct(Ur, beta))
                 -fastConvolutionalProduct(Wr,  AlgDotProduct(alph-Sigmax, beta-Sigmay)));
        print("Their product in the normal basis is: ");
        print(AB);		
}

 
 
 /***
 * Bibliography
 *
 * [CoLe2009] Jean-Marc Couveignes and Reynald Lercier. "Elliptic Basis for finite fields", 
 *  Finite Fields and their Applications, 2009.
 * 
 * [CoLe2013] Jean-Marc Couveignes and Reynald Lercier. "Fast construction of irreducible 
 *  polynomials over finite fields", Israel Journal of Mathematics, 194 (2013), pp. 77-105.
 *
 * [EzSa2018] Tony Ezome and Mohamadou Sall. "Normal bases from 1-dimensional algebraic groups".
 *  Journal of Symbolic Computation, https://doi.org/10.1016/j.jsc.2019.07.002 2019..
 *
 **************************************************************************************************/
/***
*Examples of use of the affalgpnormbasis package
*
*/

/* Importation of functions */
read("affalgpnormbasis.gp");

/**************************************************** Artin Schreier Normal Basis Example :
p = 5, q = p^3, and d = 5
Note: For examples with large finite fields the user has to manage the stack size.
                                                                      *********************************************************/
addgroupnormbasistest() =
{
	my(p = 5, d = 5, Fp = ffgen(p), Fq = ffgen(5^3, 'r));
	my(N, A, B);
	     
		 print("!!! \e[1;34mThis function allows us to test the normal basis using Artin-Schreier theory\e[0m !!!");
		 print("**********************************************************************************");
		 print("******************************** \e[1;34mChosen parameters\e[0m *******************************");
		 print("**********************************************************************************");
         print("   The characteristic p =" p ", the degree d = " d ", and q = " p^3);
		 print("**********************************************************************************");
		 print("************************* \e[1;34mConctruction of the normal basis\e[0m ***********************");
		 print("**********************************************************************************");
		 N = addgroupnormbasis(Fq, d);
		    if(type(N)=="t_STR", return(N));
		 print("A vector N, supposed to form a normal basis, is found");
		 print("N = "N);
	     \\print("N = "VecrepresentInExtendedPolBasis(N, Fq));		 
		 print("Is N a normal basis? (1=yes, 0=no): " isnormal(N[1], d));
		 print("For a relative representation of N use 'VecrepresentInExtendedPolBasis'");
		 print("**********************************************************************************");
		 print("********************** \e[1;34mComplexity of the normal basis\e[0m ****************************");
		 print("**********************************************************************************");
	     print("Note: The complexity must be less or equal to 3*p-2=" 3*p-2);						 
         print("We found the following complexity: " normalBasisWeight(N));
		 
		 /* Multiplication of two elements A and B in the normal basis */
		 print("**********************************************************************************");
		 print("******************** \e[1;34mMultiplication in the normal basis\e[0m **************************");
		 print("**********************************************************************************");
		 A = random(N[1]);
		 B = random(N[1]);
		 addgroupnormbasisfastmult(A, B, N);
		 
	return("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! End Test !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
		 
}


/********************************** Kummer Normal Basis Example :
p = 11, q = p^2, and d = 5
Note: For examples with large finite fields the user has to manage the stack size.
                                                                      *********************************/

multgroupnormbasistest() = 
{	 
     my(p = 11, d = 5, Fp = ffgen(p), q=p^2, Fq = ffgen(q, 'r));
	     
		 print("   !!! \e[1;34mThis function allows us to test the normal basis using Kummer theory\e[0m !!!");
		 print("**********************************************************************************");
		 print("******************************** \e[1;34mChosen parameters\e[0m *******************************");
		 print("**********************************************************************************");
         print("   The characteristic p =" p ", the degree d = " d ", and q = " q);
	     N = multgroupnormbasis(Fq, d);
		    if(type(N)=="t_STR", return(N));
         print("**********************************************************************************");
		 print("************************* \e[1;34mConctruction of the normal basis\e[0m ***********************");
		 print("**********************************************************************************");			
         print("\e[1;34mA vector N, supposed to form a normal basis, is found\e[0m");
	     print("N = "N);
		 \\print("N = "VecrepresentInExtendedPolBasis(N, Fq));
		 print("Is N a normal basis? (1=yes, 0=no): " isnormal(N[1], d));
		 print("For a relative representation of N use 'VecrepresentInExtendedPolBasis'");
		 print("**********************************************************************************");
		 print("********************** \e[1;34mComplexity of the normal basis\e[0m ****************************");
		 print("**********************************************************************************");
	     print("Note: The complexity must be less or equal to 3*p-2=" 3*p-2);						 
         print("We found the following complexity: " normalBasisWeight(N));
		 
		 /* Multiplication of two elements A and B in the normal basis */
		 print("**********************************************************************************");
		 print("******************** \e[1;34mMultiplication in the normal basis\e[0m **************************");
		 print("**********************************************************************************");
		     A = random(N[1]);
		     B = random(N[1]);
		     multgroupnormbasisfastprod(A, B, N);
		 
	return("!!!!!!!!!!!!!!!!!! End !!!!!!!!!!!!!!!!!!");
}



/********************************** Lucas Torus Normal Basis Example :
p = q = 7, d = 4, and D = 3
GTq = (5, 1) generates the group T3(GF(7))
t = (0, 3) generates the 4-torsion subgroup
                                                                      *********************************/
luctorusnormbasistest() = 
{
	my(p = 7, q = 7, Fq = ffgen(q), d=4, D = Fq^0*3);
	my(TD = lucasParameters(D), TDd);
	until(TDd[5] == [5, 1], TDd = lucasParametersExtend(TD, d));		
	my([Dd, rFqd, mFqd, imFqd, GTq] = TDd);
    my(b, Gg, t);
    my(bt, cstc, csta, cstb, lucB, LucBtest);
	my(A, alph, Atest=0, B, beta);
    my(v0b, Zi0, Iota, R, Ur, Wr, Uri, Sigmax, Sigmay);	
	
	    b = lucasFindFiberElement(TD, d, GTq);
        Gg = lucasSubs(TDd, [b[1]^q, b[2]^q], b);
        t = ffmap(imFqd, Gg);
            /* testing if the point t is of order d, OK it works */
                      \\print(lucasOrderTwist(TD, t) == d);
	
	    /* Parameters */
	         print("   !!! \e[1;34mThis function allows us to test the normal basis using Lucas torus\e[0m !!!");
		     print("**********************************************************************************");
		     print("******************************** \e[1;34mChosen parameters\e[0m *******************************");
		     print("**********************************************************************************");	
	         print("   The characteristic p, and q are equal : p = q = " 7);
             print("   Generator GTq of the torus over GF("p") : " GTq);
             print("   Element b in the pre-image of GTq : " b);
             print("   Generator t of the d-torsion T[d] : " t);
             print("   One element ti in T[d] satisfies ti = Frob(b) - b given by");
             print("       lucaSubs(TDd, [b[1]^q, b[2]^q], b) = " lucasSubs(TDd, [b[1]^q, b[2]^q], b), " and t = lucasExponentiation(TD, ti, 3)");
			 
		/* determination of the constants */
		     print("**********************************************************************************");
		     print("*********************** \e[1;34mDetermination of the constants\e[0m **************************");
			 print("**********************************************************************************");
             until(lucasExponentiation(TD, bt, d) != [1, 0], bt = lucasRandomPara(TD));
             cstc = lucasUot(TD, t, bt);
             for(k=1, d-1, cstc = cstc + lucasUkt(TD, t, k, bt));
                 if( cstc == 0,
                                csta = D^0; cstb = D^0 / d,
                                csta = 1 / cstc; cstb = D^0*0
                   );
                 /* Testing constants */
                    print("The constants are [cstc, csta, cstb] = ", [cstc, csta, cstb]);
                    print("They satisfy csta*cstc + d*cstb = " csta*cstc+d*cstb);
					
		/* Construction of the normal element */
		    print("**********************************************************************************");
		    print("************************* \e[1;34mConctruction of the normal basis\e[0m ***********************");
		    print("**********************************************************************************");
            [cstad, cstbd] = ffmap(mFqd, [csta, cstb]);
            Nelt = cstad*lucasUot(TDd, ffmap(mFqd, t), b) + cstbd;				    	 
            lucB = vector(d); lucB[1] = Nelt;
                    for(k=1, d-1,
                             lucB[k+1] = cstad*lucasUkt(TDd, ffmap(mFqd, t), k, b) + cstbd
                        );						
					print("A vector N, supposed to form a normal basis, is found");
	                print("N = "lucB);
		            print("Is N a normal basis? (1=yes, 0=no): " isnormal(Nelt, d));
					

                    /* Testing the normal basis */
					print("Testing the normal basis");
                       LucBtest = vector(d);
					   LucBtest[1] = Nelt;
                       for(k=1, d-1,
                                LucBtest[d-k+1] = Nelt^(q^k);
                           );
                    print("Vector lucB computed with our functions (ie our Normal Basis N):" );
					print(lucB);
                    print("Vector LucBtest given by the conjugates of the normal element Nelt:");
					print(LucBtest);
                    print("Equality test : Is lucB eqal to LucBtest? (1=yes and 0=no) " lucB == LucBtest);
					
		/* Multiplication of two elements A and B in a Lucas torus normal basis */
		    print("**********************************************************************************");
		    print("******************** \e[1;34mMultiplication in the normal basis\e[0m **************************");
		    print("**********************************************************************************");
			A = random(lucB[1]);
		    B = random(lucB[1]);
			luctorusnormbasisfastmult(A, B, TD);
			
	return("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! End Test !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
}

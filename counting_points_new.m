
// This code has been developed by the contributions of Valerio Dose, Guido Lido, Pietro Mercuri, Claudio Stirpe

// This file contains three functions:
// shipoints computes the number of points of a Shimura curve X_0^D(N) over a finite field;
// shiweil computes the real Weil polynomial of X_0^D(N);
// prepare_forms computes the input "forms" necessary for shipoints.




/*

The Main Function is shipoints, described here:

Given the Shimura curve X_0^D(N) and its Atkin-Lehner quotient X for a certain subgroup of the Atkin-Lehner involutions this function compute the genus and the number of F_{q^i}-rational points of X.

More precisely, we have the following.

Input:
1) q must be a prime less than 100 and coprime with D*N;
2) D must be positive integer such that there only an even number of distinct primes dividing it;
3) N must be positive integer coprime with D;
4) forms is a list whose elements are lists [*n,orbits*] of two elements:
  - n is the level;
  - orbits is the list of Galois orbit of newforms of level n whose elements are lists [*ALEV,HEV_1,...,HEV_a*] representing a single Galois orbit,
    - ALEV is a list [*e_1,...,e_b*] where e_j is the eigenvalue of the Atkin-Lehner operator w_p for p the j-th prime dividing the level n (hence b is the number of primes dividing n) acting on any newform of the orbit;
    - HEV_i is the eigenvalue of the Hecke operator T_q acting on the i-th newform in the Galois orbit.
WARNING: forms must contain exactly one list for each n positive divisor of D*N.
5) ALprimes is a sequence of sets where each set corresponds to one Atkin-Lehner operator w_M and the set contains the indices of primes dividing M, the indexing is given ordering by increasing order the primes dividing level;
6) m is a positive integer indicating the maximal power of q with respect to which the function will compute the number of points over the corresponding finite field;
7) 10^(-eps) is the approximation required to accept that the roots of the characteristic polynomial of Frobenius are actually integers.

Output:
1) g is the genus of X;
2) v is the sequence of the number of F_{q^j}-rational points of X for j=1 to j=m;
3) t is the sequence of the roots of the characteristic polynomial of q^j-Frobenius on the Jacobian of X for j=1 to j=m.

*/



// loading data on Hecke eigenvalues obtained from the LMFDB
// in a list named dataByLevel.
// This line should remain commented out if you are not using pre-computed trace data. 

	// load "traces10k.m";


// traces_to_forms: given a list "trace_data" of Hecke traces
// and q, D, N as in inputs  1), 2), 3) for the main 
// function shipoints as noted above, returns data in the list
// of the format of "forms" in 4) above. 

// This can be used for the function shipoints if one loads
// in pre-computed data of Hecke traces, as used in the line
// commented above, rather than using data 
// already in the format used for the "forms" input for the
// shipoints function OR computing the data by scratch 
// using the prepare_forms function defined below. If loading in the
// traces10k.m file as in the above line, for example, one can compute 
// point counts for X_0^D(N) over F_q with the following command:
// 				shipoints(q, D, N, traces_to_forms(dataByLevel, q, D, N) : ALprimes:=[], m:=1, eps:=3)
// One can work with more general quotients and obtain counts over F_q^k for k>1 by adjusting the 
// ALprimes and m arguments, respectively, as described above for the main function shipoints. 

traces_to_forms := function(trace_data, q, D, N)
	forms:=[**];
	p:=2;
	k:=1;
	while p lt q do
  	k:=k+1;
		p:=NthPrime(k);
	end while;
	divs:=Divisors(D*N);
	for n in divs do
  	leveln:=[*n*];
		orbits:=[**];
  	dim1:=#trace_data[n];
  	for cont:=1 to dim1 do
 			ff:=[**];
 			Append(~ff,trace_data[n,cont,6]);
			w:=trace_data[n,cont,3];
			for c in [1..w] do
      	Append(~ff,trace_data[n,cont,7,c][k]);
    	end for;
			Append(~orbits,ff);
		end for;
		Append(~leveln,orbits);
		Append(~forms,leveln);
	end for;

	return forms;
	
end function;



// main function shipoints, with input and output as described above
shipoints:=function(q, D, N, forms : ALprimes:=[], m:=1, eps:=3) 
	level:=D*N;
	if (D lt 1) or not(D in Integers()) then
	  return "Error: D must be a positive integer.";
	elif (N lt 1) or not(N in Integers()) then
	  return "Error: N must be a positive integer.";
  elif q ge 100 then
	  return "Error: q must be less than 100.";
	elif GCD(q,level) gt 1 then
	  return "Error: q must be coprime with the level D*N.";
	elif (m lt 1) or not(m in Integers()) then
	  return "Error: m must be a positive integer.";
	else
		K<x>:=PolynomialRing(ComplexField());
		DIVILEV:=Divisors(level);
		priLEV:=PrimeDivisors(level);
		VLEV:=[]; // p-adic valuation of level for each prime p dividing level
		for p in priLEV do
			Append(~VLEV,Valuation(level,p));
		end for;
		g:=0;
		Hecke:=[]; // sequence of Hecke eigenvalues of the newforms
		for n in DIVILEV do 
			if IsDivisibleBy(n,D) then
		  	orbits:=[**];
				DIVILEVn:=Divisors(n);
				priLEVn:=PrimeDivisors(n);
				VLEVn:=[];
				for p in priLEV do
					Append(~VLEVn,Valuation(n,p));
				end for;
				nozeri:={}; // primes in ALprimes
				for J in ALprimes do 
					nozeri:=nozeri join J;
				end for;
				zeri:={}; // primes not in ALprimes
				for i in [1..#priLEV] do
					if not i in nozeri then
						zeri:=zeri join {i};
					end if;
				end for;
				
				// Taking the Galois orbits of newforms of level n
				for FF in forms do
					if FF[1] eq n then
						orbits:=FF[2];
						break FF;
					end if;
				end for;

				// Computing multiplicity m_f
				for ff in orbits do
					m_f:=0;
					Hf0p:=[]; // number of forms with eigenvalue +1 with respect to the Atkin-Lehner operator w_p for each prime p dividing level
					Hf0m:=[]; // number of forms with eigenvalue -1 with respect to the Atkin-Lehner operator w_p for each prime p dividing level
					Hf0:=[]; // number of forms with eigenvalue +1 or -1 with respect to the Atkin-Lehner operator w_p for each prime p dividing level
					H1:=1; // will be the product of the Hf0
					autoVal:=[];
					for i in [1..#priLEV] do
						dif:=VLEV[i];
						k1:=0;
						for j in [1..#priLEVn] do
							if priLEVn[j] eq priLEV[i] then
								k1:=j;
								break j;
							end if;
						end for;
						if k1 eq 0 then // it may happen that p does not divide n
						  autoV:=1;
							autoVal[i]:=autoV;	
						else 
							autoV:=ff[1][k1]; //dataByLevel[n,cont,6][k1];
							autoVal[i]:=autoV;
							dif:=dif-VLEVn[i];
						end if;
						parte2:=Floor((1+(-1)^dif)/2);
						zp:=Floor((dif+1+parte2*autoV)/2);
						Append(~Hf0,dif+1);
						Append(~Hf0p,zp);
						Append(~Hf0m,dif+1-zp);
					end for;
					for t in zeri do 
						H1:=H1*Hf0[t];
					end for;

					// Subsets of J with even intersections
					vector:=Subsets(nozeri);
					for u in vector do
						check:=1;
						for J in ALprimes do 
							if not IsEven(#(J meet u)) then
								check:=0;
							end if;
						end for;
						if check eq 0 then
							Exclude(~vector,u);
						end if;
					end for;
					for u in vector do
						H:=H1;
						for t in nozeri do
							if IsEven(#PrimeDivisors(GCD(priLEV[t],D))) then 
								segno:=1;
							else 
								segno:=-1;
							end if;
							if t in u then
								if segno eq 1 then
									H:=H*Hf0m[t];
								else
									H:=H*Hf0p[t];
								end if;
							else
								if segno eq 1 then
									H:=H*Hf0p[t];
								else
									H:=H*Hf0m[t];
								end if;
							end if;
						end for;
						m_f:=m_f+H; 
					end for;
					// End computing multiplicites m_f
					
					// Collecting Hecke eigenvalues
					for cont in [1..m_f] do 
						for c in [2..#ff] do
							Append(~Hecke,ff[c]);
							g:=g+1;
						end for;
					end for;
				end for; // ff
			end if; // D|n
		end for; // n
		
		// Roots of the charcteristic polynomial of q-Frobenius
		t:=[];
		for i:=1 to #Hecke do
			d:=Roots(x^2+q-Hecke[i]*x,ComplexField());
			Append(~t,d[1][1]);
			Append(~t,d[2][1]);
		end for; 
		v:=[];
		
		// Computing the number of points of the curve over F_{q^j}
		for j:=1 to m do        
			e:=0;
			for i:=1 to #Hecke do
				e:=e+t[2*i]^j+t[2*i-1]^j;
			end for;
			eint:=Round(Real(e));
			if Abs(e-eint) lt 10^(-eps) then
  			Append(~v,q^j+1-eint);
				out:=true;
			else
			  out:=false;
			end if;
		end for;
			
		if out then	
		  return g, v, t;
		else
		  return "Error: precision is not enough to recognize integers.";
		end if;
	end if;
end function; 



// Function shiweil.

// Given the Shimura curve X_0^D(N) and its Atkin-Lehner quotient X for a certain subgroup of the Atkin-Lehner involutions this function computes the real Weil polynomial of X.
// q, D, N, forms, and ALprimes are the same input as the function shipoints above.
// j is the power of q giving the finite field F_{q^j} with respect to which we want to compute the real Weil polynomial.

shiweil:=function(q,j,D,N,forms:ALprimes:=[]) 
  K<y>:=PolynomialRing(ComplexField());
  P<x>:=PolynomialRing(Rationals());
  g,v,t:=shipoints(q,D,N,forms:ALprimes:=ALprimes);
  polcompl:=1; 
  for alpha in t do
    polcompl:=polcompl*(y-alpha^j);
  end for;
  coeff:=[];
  if polcompl ne 1 then
    for k in [1..2*g+1] do
      c:=Coefficient(polcompl,k-1);
      coeff[k]:=Floor((c+ComplexConjugate(c))/2+0.1);
    end for;
  else 
    coeff[1]:=1;
  end if;
  L:=0;
  for i in [1..2*g+1] do 
    L:=L+coeff[i]*x^(i-1); 
  end for;
  a:=[];
  for i in [1..g+1] do
    b:=Coefficients(L);
    for l in [1..2*g] do 
      Append(~b,0);
    end for;
    pol:=x^(i-1)*(x^2+q)^(g+1-i);
    a[i]:=b[2*g+2-i];
    L:=L-a[i]*pol;
  end for;
  weil:=0;
  for i in [1..#a] do
    weil:=weil+a[i]*x^(g+1-i);
  end for;
  return weil;
end function;



// Function prepare_forms.

// q, D, N are the same input as the function shipoints above.

prepare_forms:=function(q,D,N)
	forms:=[**];
	level:=D*N;
	divs:=Divisors(level);
	prdivs:=PrimeDivisors(level);
	for n in divs do
	  leveln:=[*n*];
		orbits:=[**];
		NF:=Newforms(CuspForms(n));
	  for cont:=1 to #NF do
		  ff:=[**];
		  ALn:=[**];
		  try
	      Af:=ModularAbelianVariety(NF[cont][1]);
	    catch e
	      continue;
	    end try;
		  for pp in prdivs do
		    levelAf:=Level(Af);
		    if IsDivisibleBy(levelAf,pp) then
		      Append(~ALn,Matrix(AtkinLehnerOperator(Af,pp^Valuation(levelAf,pp)))[1,1]);
		    end if;
		  end for;
		  Append(~ff,ALn);
		  aq:=Coefficient(NF[cont][1],q);
			for c in [1..#NF[cont]] do 
	      Append(~ff,Conjugate(aq,c));
	    end for;
			Append(~orbits,ff);
		end for;
		Append(~leveln,orbits);
		Append(~forms,leveln);
	end for;
	return forms;
end function;

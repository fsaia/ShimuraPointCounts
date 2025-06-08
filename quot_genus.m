// quot_genus.m
// the main function, quot_genus, computes for a given indefinite rational 
// quaternion discriminant D, positive integer N coprime to D, and Hall divisor m
// of DN, the genus of the quotient Shimura curve X_0^D(N)/<w_m>


// phi_from_fact
// Given natural N, factorization of N (list of pairs (p,a)), computes phi(N) 

phi_from_fact := function(N,F)
    P := N;
    for i in [1..#F] do
        P := P*(1-1/(F[i][1]));
    end for;
    return P;
end function;



// psi_from_fact 
// Given natural N, factorization of N (list of pairs (p,a)), computes psi(N)

psi_from_fact := function(N,F)
    M := 1;
        for i in [1..#F] do
            M := M * (F[i][1]+1)*F[i][1]^(F[i][2]-1);
        end for;
    return M;
end function;



// e1_from_fact: Given factorizations F_D and F_N of a rational quaternion discriminant D and
// a natural number N which is coprime to D, respectively, returns e_1(D,N)

e1_from_facts := function(F_D,F_N,N)
    if (N mod 4) eq 0 then
        return 0;
    else
        P := 1;
        for i in [1..#F_D] do
            P := P*(1-KroneckerSymbol(-4,F_D[i][1]));
        end for;
        for i in [1..#F_N] do
            P := P*(1+KroneckerSymbol(-4,F_N[i][1]));
        end for;
        return P;
    end if; 
end function;



// e3_from_fact: Given factorizations F_D and F_N of a rational quaternion discriminant D and
// a natural number N which is coprime to D, respectively, returns e_3(D,N)

e3_from_facts := function(F_D,F_N,N)
    if (N mod 9) eq 0 then
        return 0;
    else
        P := 1;
        for i in [1..#F_D] do
            P := P*(1-KroneckerSymbol(-3,F_D[i][1]));
        end for;
        for i in [1..#F_N] do
            P := P*(1+KroneckerSymbol(-3,F_N[i][1]));
        end for;
        return P;
    end if; 
end function;



// genus

genus := function(D,N)
    FD := Factorization(D);
    FN := Factorization(N);
    return (1+phi_from_fact(D,FD)*psi_from_fact(N,FN)/12 - e1_from_facts(FD,FN,N)/4 - e3_from_facts(FD,FN,N)/3);
end function; 



// psi_p 
// Given natural N, prime p, computes psi_p(N) as in Ogg83 Thm 2

psi_p := function(N,p)
    k := Valuation(N,p);
    if k eq 0 then 
        return 1;
    else 
        return p^k + p^(k-1); 
    end if;
end function; 



// count_local_embeddings
// Counts number of local embeddings of order R of discriminant f^2*delta_K into order of level N in 
// quaternion algebra B of discriminant D, via Ogg83 Theorem 2 

count_local_embeddings := function(D,N,p,delta_K,f)

    assert IsDivisibleBy(D*N,p);
    
    if (f mod p eq 0) then 
        symbol_R_p := 1;
    else
        symbol_R_p := KroneckerSymbol(delta_K,p);
    end if; 

    if (D mod p) eq 0 then // case i
        return 1 - symbol_R_p;

    elif (N mod p) eq 0 then 

        k := Valuation(N,p); //3
        l := Valuation(f,p); //0

        if k eq 1 then // case ii
            return 1 + symbol_R_p;

        elif k ge (2+2*l) then  // case iii a
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*psi_p(f,p); 
            else
                return 0;
            end if; 

        elif k eq (1+2*l) then  // case iii b
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*psi_p(f,p);
            elif KroneckerSymbol(delta_K,p) eq 0 then
                return p^l;
            else 
                return 0;
            end if;

        elif k eq 2*l then  // case iii c
            return p^(l-1)*(p+1+KroneckerSymbol(delta_K,p));

        elif (f^2 mod p*N) eq 0 then // case iii d
            if (k mod 2) eq 0 then
                return p^k+p^(k-1);
            else
                return 2*p^k;
            end if;

        end if;
    end if;
end function; 



// count_fixed_points
// given quaternion discriminant D, N coprime to D, m || DN, delta_K, and f, 
// computes number of f^2*delta_K-CM fixed points of w_m on X_0^D(N)
// by Eichler's Theorem, see Thm 1 in Ogg83 and eqn 4 in Ogg83

count_fixed_points := function(D,N,m,delta_K,f)
    P := 1;
    for pair in Factorization(Integers()!(D*N/m)) do 
        p := pair[1];
        P := P*count_local_embeddings(D,N,p,delta_K,f);
    end for;

    return ClassNumber(delta_K*f^2)*P;
end function; 



// sqfree_part
// given positive integer m, returns the sqfree part of m
sqfree_part := function(m)
    S := 1;
    for pair in Factorization(m) do
        v := Valuation(m,pair[1]);
        if (v mod 2) eq 1 then 
            S := S*pair[1];
        end if;
    end for;

    return S;
end function; 



// quot_genus
// given quaternion discriminant D, N coprime to D, and W a subgroup of W_0(D,N) given
// by a list [m_1, ..., m_n] of all m such that w_m in W, computes
// the genus of X_0^D(N)/W
// by Riemann--Hurwitz, also see Ogg83 eqn 3

quot_genus := function(D,N,W)

    g := genus(D,N); // genus of the top curve
    deg := #W; // degree of quotient map

    fixed_number := 0; // initializing fixed point count

    for m in [m : m in W | m ne 1] do
        
        if m eq 2 then 
            fixed_number := fixed_number + count_fixed_points(D,N,m,-4,1) + count_fixed_points(D,N,m,-8,1); 

        elif (m mod 4) eq 3 then 
            disc_K := -1*sqfree_part(m); // K = Q(sqrt(-m))
            _,f := IsSquare(Integers()!(m/sqfree_part(m)));
            fixed_number := fixed_number + count_fixed_points(D,N,m,disc_K,f) + count_fixed_points(D,N,m,disc_K,2*f);

        else
            disc_K := -4*(sqfree_part(m)); // K = Q(sqrt(-m))
            _,f := IsSquare(Integers()!(m/sqfree_part(m)));
            fixed_number := fixed_number + count_fixed_points(D,N,m,disc_K,f); 

        end if;
    end for;

    return (1/(2*deg))*(2*g-2 - fixed_number)+1;
end function;




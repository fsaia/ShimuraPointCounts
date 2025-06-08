// The aim of this code is to compute the Delta-CM locus on X^D_0(N)
// for any imaginary quadratic discriminant Delta and positive integer N coprime to
// a given quaternion discriminant D. We also provide functions e.g. for computing all primitive
// (degrees of) residue fields of Delta-CM points on X^D_0(N). 

// This is done via an isogeny-volcano approach, based on
// work of Clark--Saia 2022 in the D=1 case and work of Saia 2022 in the D>1 case 


//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// CM Points on X^D_0(N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


// CM_points_XD0_prime_power
// Input: factorization of quaternion discriminant D (even product of primes), CM conductor f, fundamental discriminant d_K, 
// prime l, exponent a at least 1
// Ouput: A pair of sequences of sequences [conductor, ram, degree, number],
// with the first sequence in the pair giving the sequence of index 2 subfields of
// ring class fields (as described in work of Jordan and Gonzalez--Rotger) which 
// arise as residue fields of f^2d_K-CM points on X^D_0(l^a) via 
    // the CM conductor of the ring class field, 
    // the ramification index w.r.t. X^D_0(l^a)-->X^D(1) (which is 1, 2, or 3), 
    // the degree over Q of the residue field, and 
    // the number of points with this residue field and ramification index. 
// The second sequence gives the same ordered information for ring class fields
// which arise as residue fields of such points.  

// Note: the elliptic-modular D=1 case of X^1_0(N) = Y_0(N) is allowed!

CM_points_XD0_prime_power := function(D_Fact, f, d_K, l, a)

    assert a ge 0; 

    L := Valuation(f,l); // "level" of d in G_{K,l,f_0}
    f_0 := IntegerRing()!(f/l^L); // coprime to l part of conductor f

    // checking that D is a quaternion discriminant and l doesn't divide D
    if #D_Fact mod 2 eq 1 then 
        return "D not a quaternion discriminant!";
    end if;

    for pair in D_Fact do 
        if pair[2] gt 1 then 
            return "D not a quaternion discriminant!";
        end if; 

        if pair[1] eq l then 
            return "level not coprime to quaternion discriminant D";
        end if; 
    end for; 

    // checking that K splits the quaternion algebra and computing
    // b = number of primes dividing D which are inert in K
    b := 0; 
    for pair in D_Fact do 
        if KroneckerSymbol(d_K,pair[1]) eq 1 then 
            return "K does not split the quaternion algebra of discriminant D";
        elif KroneckerSymbol(d_K,pair[1]) eq -1 then 
            b := b+1; 
        end if;
    end for; 

    // initializing CM points list 
    points := [*[],[]*];

    // setting splitting behavior of l in K, to be used often
    symbol_l_K := KroneckerSymbol(d_K,l);

    // D_check: true if all primes dividing D are ramified in K, false otherwise 
    D_check := true; 
    for pair in D_Fact do
        if (KroneckerSymbol(d_K,pair[1]) eq -1) then
            D_check := false;
            break;
        end if;
    end for; 


    // Case all primes dividing D ramify in K
    if D_check eq true then 
        
        // 6.1: General Case 

        // Type I
        if (f_0^2*d_K eq -4) and (L eq 0) then
            Append(~points[1],[l^a*f,2,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        elif (f_0^2*d_K eq -3) and (L eq 0) then
            Append(~points[1],[l^a*f,3,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        else 
            Append(~points[1],[l^a*f,1,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        end if; 

        // Type II
        if a le L then
            Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]); 
        end if;

        if L eq 0 then 

            if (f_0^2*d_K eq -4) then 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,2,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,2,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;

            elif (f_0^2*d_K eq -3) then
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,3,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,3,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;

            else 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,1,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,1,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;
            end if; 

        end if;

        // Type X
        if (L ge 1) and (a gt L) and (symbol_l_K eq 1) then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]); 
        end if;

        // 6.2: l > 2
        if l gt 2 then 

            // Type V
            if (L ge 2) then 
                for c in [1..Min(a-1,L-1)] do 
                    Append(~points[2],[l^(Max(a-2*c,0))*f,1,2*ClassNumber((l^(Max(a-2*c,0))*f)^2*d_K),2^b*((l-1)/2)*l^(Min(c,a-c)-1)]);
                end for;
            end if;

            // Type VI
            if (a gt L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                Append(~points[1],[l^(Max(a-2*L,0))*f,1,ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b]);
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*(l^(Min(L,a-L))-1)/2]);
            end if; 

            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 0) then 

                // Type VII
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-1)/2)*l^(Min(L,a-L)-1)]);

                // Type VIII
                Append(~points[1],[l^(Max(a-2*L-1,0))*f,1,ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b]);
                if (a-L-1 gt 0) then 
                    Append(~points[2],[l^(Max(a-2*L-1,0))*f,1,2*ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(l^(Min(L,a-L-1))-1)/2]);
                end if; 

            end if; 
             
            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 1) then

                // Type IX
                Append(~points[1],[l^(Max(a-2*L,0))*f,1,ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b]);
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-2)*l^(Min(L,a-L)-1)-1)/2]);

                // Type XI
                if (a ge L+2) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[l^(Max(a-2*L-h,0))*f,1,2*ClassNumber((l^(Max(a-2*L-h,0))*f)^2*d_K),2^b*(l-1)*l^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            end if;

        elif l eq 2 then 

            // 6.3: l=2, unramified 
            if symbol_l_K ne 0 then 

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if;

                // Type V_2
                if (L ge a) and (a ge 3) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                if (a ge L+1) and (L ge 3) then 
                    Append(~points[1],[2^(Max(a-2*L+2,0))*f,1,ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^b*2]);
                    Append(~points[2],[2^(Max(a-2*L+2,0))*f,1,2*ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^b*(2^(Min(a-L+1,L-1)-2)-1)]);
                end if;

                // Type V_4
                for c in [2..Min(L-2,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for; 

                // Type VI
                if (a ge L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2^(Min(L,a-L)-1)]);
                end if;

                // Type XI
                if (a ge L+2) and (L ge 1) and (symbol_l_K eq 1) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[2^(Max(a-2*L-h,0))*f,1,2*ClassNumber((2^(Max(a-2*L-h,0))*f)^2*d_K),2^b*2^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            // 6.4: l=2, ord_2(d_K) = 2
            elif Valuation(d_K,2) eq 2 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[1],[2^(Max(a-2*L,0))*f,1,ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2]);
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*(2^(Min(L,a-L)-2)-1)]);
                end if; 

                // Type VIII

                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*2^(Min(L,a-1-L)-1)]);
                    end if;

                end if;


            // 6.5: l=2, ord_2(d_K) = 3
            elif Valuation(d_K,2) eq 3 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2^(Min(L,a-L)-2)]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[1],[2^(Max(a-2*L-1,0))*f,1,ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*2]);
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(2^(Min(L,a-1-L)-1)-1)]);
                    end if;
                end if;
            end if;
        end if;


    // Case some prime dividing D is inert in K
    elif D_check eq false then 

        // 6.1: General Case 

        // Type I
        if (f_0^2*d_K eq -4) and (L eq 0) then
            Append(~points[2],[l^a*f,2,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        elif (f_0^2*d_K eq -3) and (L eq 0) then
            Append(~points[2],[l^a*f,3,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        else 
            Append(~points[2],[l^a*f,1,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        end if; 

        // Type II
        if a le L then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^(b)]); 
        end if;

        if L eq 0 then 

            if (f_0^2*d_K eq -4) then 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,2,2*ClassNumber((l^(a-1)*f)^2*d_K),2^(b)]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,2,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;

            elif (f_0^2*d_K eq -3) then
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,3,2*ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,3,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;

            else 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,1,2*ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,1,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;
            end if; 

        end if;

        // Type X
        if (L ge 1) and (a gt L) and (symbol_l_K eq 1) then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^(b+1)]); 
        end if;

        // 6.2: l > 2
        if l gt 2 then 

            // Type V
            if (L ge 2) then 
                for c in [1..Min(a-1,L-1)] do 
                    Append(~points[2],[l^(Max(a-2*c,0))*f,1,2*ClassNumber((l^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*((l-1)/2)*l^(Min(c,a-c)-1)]);
                end for;
            end if;

            // Type VI
            if (a gt L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*(l^(Min(L,a-L)))]);
            end if; 

            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 0) then 

                // Type VII
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-1))*l^(Min(L,a-L)-1)]);

                // Type VIII
                Append(~points[2],[l^(Max(a-2*L-1,0))*f,1,2*ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(l^(Min(L,a-L-1)))]);

            end if; 
             
            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 1) then

                // Type IX
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-2)*l^(Min(L,a-L)-1))]);

                // Type XI
                if (a ge L+2) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[l^(Max(a-2*L-h,0))*f,1,2*ClassNumber((l^(Max(a-2*L-h,0))*f)^2*d_K),2^(b+1)*(l-1)*l^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            end if;

        elif l eq 2 then 

            // 6.3: l=2, unramified 
            if symbol_l_K ne 0 then 

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if;

                // Type V_2
                if (L ge a) and (a ge 3) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                if (a ge L+1) and (L ge 3) then 
                    Append(~points[2],[2^(Max(a-2*L+2,0))*f,1,2*ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^(b+1)*2^(Min(a-L+1,L-1)-2)]);
                end if;

                // Type V_4
                for c in [2..Min(L-2,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for; 

                // Type VI
                if (a ge L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L)-1)]);
                end if;

                // Type XI
                if (a ge L+2) and (L ge 1) and (symbol_l_K eq 1) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[2^(Max(a-2*L-h,0))*f,1,2*ClassNumber((2^(Max(a-2*L-h,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            // 6.4: l=2, ord_2(d_K) = 2
            elif Valuation(d_K,2) eq 2 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*(2^(Min(L,a-L)-2))]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-1-L)-1)]);
                    end if;

                end if;

            // 6.5: l=2, ord_2(d_K) = 3
            elif Valuation(d_K,2) eq 3 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L)-2)]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^(b+1)*(2^(Min(L,a-1-L)-1))]);
                    end if;
                end if;
            end if;
        end if;
    end if; 

    // sort both sequences of point information by conductor (hence also by degree)
    points := [* Sort(points[1],func<x,y | x[1]-y[1]>), Sort(points[2],func<x,y | x[1]-y[1]>) *];
    return points;

end function; 



// CM_points_XD0
// Input: quaternion discriminant D (even product of primes), CM conductor f, 
// fundamental discriminant d_K, positive integer N
// Ouput: A pair of sequences of sequences [conductor, ram, degree, number],
// with the first sequence giving the sequence of index 2 subfields of 
// ring class fields which arise as residue fields of f^2d_K-CM points on X^D_0(N) via 
    // the CM conductor, 
    // the ramification index w.r.t. X^D_0(N)-->X(1) (which is 1, 2, or 3), 
    // the degree over Q of the residue field, and 
    // the number of points with this residue field and ramification index. 
// The second sequence gives the same ordered information for ring class fields
// which arise as residue fields of such points.  

// Note: the elliptic-modular D=1 case of X^1_0(N) = X_0(N) is allowed!

CM_points_XD0 := function(D, f, d_K, N)

    N_Fact := Factorization(N); 
    r := #N_Fact;
    D_Fact := Factorization(D);

    // N = 1 case, X^D_0(N) = X^D(1)
    if N eq 1 then 

        // checking that D is a quaternion discriminant
        if #D_Fact mod 2 eq 1 then 
            return "D not a quaternion discriminant!";
        end if;

        for pair in D_Fact do 
            if pair[2] ne 1 then 
                return "D not a quaternion discriminant!";
            end if; 
        end for; 

        // checking that K splits the quaternion algebra and computing
        // b = number of primes dividing D which are inert in K
        b := 0; 
        for pair in D_Fact do 
            if KroneckerSymbol(d_K,pair[1]) eq 1 then 
                return "K does not split the quaternion algebra of discriminant D";
            elif KroneckerSymbol(d_K,pair[1]) eq -1 then 
                b := b+1; 
            end if;
        end for; 

        // D_check: true if all primes dividing D are ramified in K, false otherwise 
        D_check := true; 
        for pair in D_Fact do
            if (KroneckerSymbol(d_K,pair[1]) eq -1) then
                D_check := false;
                break;
            end if;
        end for; 

        // Case all primes dividing D ramified in K
        if D_check eq true then 
            return [*[[f,1,ClassNumber(f^2*d_K),2^b]], [] *];

        // Case some prime dividing D inert in K
        elif D_check eq false then 
            return [*[], [[f,1,2*ClassNumber(f^2*d_K),2^b]] *];
        end if; 

    // N > 1 case
    elif N gt 1 then 

        // factors for creating cartesian product of information on pts at prime power levels
        prime_level_factors := [];
        for i in [1..r] do 

            // output list from prime_power function
            prime_power_pts := CM_points_XD0_prime_power(D_Fact,f,d_K,N_Fact[i][1],N_Fact[i][2]);

            if Type(prime_power_pts) eq MonStgElt then
                return prime_power_pts; // returns relevant string if K doesn't split B_D or level N not coprime to D
            end if;

            // condensing information to single sequence of pts, each a list with four entries:
                // field type: "NR" for ring class field or "R" for index 2 subfield thereof
                // conductor: CM conductor of the corresponding 
                // ram: ramification index w.r.t map X^D_0(l^a)-->X^D(1)
                // number: number of pts with this res fld and ramification index 
            prime_power_pts_factor := []; 

            // appending rational ring class field residue field pts
            for pt in prime_power_pts[1] do 
                Append(~prime_power_pts_factor,[*"R",pt[1],pt[2],pt[4]*]);
            end for;

            // appending ring class field residue field pts
            for pt in prime_power_pts[2] do
                Append(~prime_power_pts_factor,[*"NR",pt[1],pt[2],pt[4]*]);
            end for; 

            Append(~prime_level_factors,prime_power_pts_factor); 

        end for; 

        // creating cartesian product of information on pts at prime power levels
        prime_level_product := CartesianProduct(prime_level_factors); 

        // initializing list of infromation on CM points on X_0(N) to output
        points := [*[],[]*];

        for pt_tuple in prime_level_product do 

            s := #[i : i in [1..r] | pt_tuple[i][1] eq "NR"];
            conductors := [(Integers() ! pt[2]) : pt in pt_tuple]; 
            cond_lcm := Lcm(conductors); 

            ram := 1;
            for i in [1..r] do
                if pt_tuple[i][3] ne 1 then
                    ram := pt_tuple[i][3];
                    break;
                end if; 
            end for;

            // product of numbers of points at each prime power level 
            count := 1;
            for i in [1..r] do
                count := count*pt_tuple[i][4];
            end for; 

            // Case: all residue fields index 2 subfields of ring class fields 
            if s eq 0 then 
                Append(~points[1],[cond_lcm,ram,ClassNumber(cond_lcm^2*d_K),count]);

            // Case: at least one residue field is a ring class field
            else 
                Append(~points[2],[cond_lcm,ram,2*ClassNumber(cond_lcm^2*d_K),2^(s-1)*count]);
            end if; 

        end for;

        // sort list of points by conductor (hence also by degree)
        points := [* Sort(points[1],func<x,y | x[1]-y[1]>), Sort(points[2],func<x,y | x[1]-y[1]>) *];
        return points;

    end if; 
end function; 

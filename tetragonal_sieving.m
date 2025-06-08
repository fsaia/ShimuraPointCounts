// We use various information and techniques (including genus computations, known gonalities, 
// Castelnuovo--Severi arguments, finite field point counts, checks on automorphism groups, and checks for 
// rational CM points on Atkin--Lehner quotients) to narrow the tetragonal candidates listed in 
// `tetragonal_candidates.m`, either by identifying them as tetragonal (over $\mathbb{Q}$ or geometrically)
// or proving they are not tetragonal (over $\mathbb{Q}$ or geometrically). 

// List of all 516 geometrically tetragonal candidate pairs (see the file tetragonal_checks.m for
// the definition). 
load "tetragonal_candidates.m";

// loading quot_genus.m, which contains the genus(D,N) function for the genus of X_0^D(N)
load "quot_genus.m";

// loading AL_identifiers.m, which contains code for working with unique identifiers 
// for each subgroup of the full Atkin--Lehner group W_0(D,N) of X_0^D(N). 
load "AL_identifiers.m";

// loading known_gonalities lists
load "known_gonalities.m";

// loading finite field point counts code
load "point_counts_10k.m";

// Loading list of some pairs which we know have no
// involutions other than the Atkin--Lehner involutions 
load "all_atkin_lehner_10k.m";


// Hall_Divisors : given positive integer N, returns sequence of all Hall Divisors d || N. 
Hall_Divisors := function(N)
    assert N ge 1;
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1];
end function;


geom_tetragonal_by_AL_2 := [];
geom_tetragonal_by_AL_4 := [];
not_geom_tetragonal_by_CS_2 := [];
not_geom_tetragonal_by_CS_4 := [];
not_geom_tetragonal_by_CS_4_with_W := [];
hypell_simple_quotient_candidates := [];

// first, we rid of pairs which are geometrically tetragonal via having a (sub) hyperelliptic
// simple AL quotient (currently this only does it for quotient genus up to 2) or a
// AL quotient by a group of order 4 with genus 0. Then, we run CS sieves. 
for pair in tetragonal_candidates do 
    D := pair[1];
    N := pair[2];
    HD := HallDivisors(D*N);
    g_2quot_min := Min([quot_genus(D,N,[1,m]) : m in HD | m gt 1]);
    gtop := genus(D,N);

    // X_0^D(N)/<w_m> is geometrically sub-hyperelliptic for some m
    if g_2quot_min le 2 then
        Append(~geom_tetragonal_by_AL_2,pair); 

    else
        g_4quot_min := Min([quot_genus(D,N,gens_to_identifier(D*N,{p[1],p[2]})) : p in CartesianProduct(HD,HD) | (p[1] gt 1) and  (p[2] gt p[1])]);
        
        // witness geometrically tetragonal AL quotient map of degree 4
        if g_4quot_min eq 0 then 
            Append(~geom_tetragonal_by_AL_4,pair); 
        end if;  
    end if; 


    if not ((pair in geom_tetragonal_by_AL_2) or (pair in geom_tetragonal_by_AL_4)) then

        // In this case, we try to rule out X_0^D(N) being tetragonal using CS arguments
        // involing AL quotients. For this, it is helpful to note which quotients
        // X_0^D(N)/<w_{m1}> are not hyperelliptic

        // If we know X_0^D(N) has only Atkin--Lehner involutions, then no curve
        // X_0^D(N)/<w_{m1}> can be hyperelliptic (as then it would be hyperelliptic
        // by an Atkin--Lehner involution, and X_0^D(N) would have been realized as 
        // being tetragonal in the above parts).
        // Otherwise, we determine curves X_0^D(N)/<w_{m1}> which are not geometrically 
        // hyperelliptic via a CS check involving a further AL quotient
        if not (pair in all_atkin_lehner_10k) then 
            for m1 in [m1 : m1 in HD | m1 gt 1] do 
                g1 := quot_genus(D,N,[1,m1]);
                g2 := Min([quot_genus(D,N,gens_to_identifier(D*N,{m1,m2})) : m2 in HD | (m2 ne 1) and (m2 ne m1)]);
                assert g2 gt 0; // this should go through via g_4quot_min check 
                if g1 le 2*g2 + 1 then // CS check required to be hyperelliptic via non-Atkin-Lehner involution
                    // CS check did not succeed, so we further check using the Hasegawa criterion to 
                    // try to rule out the possibility of X_0^D(N)/<w_{m1}> being hyperelliptic
                    if (Integers()!(g1) mod 2 eq 0) then 
                        gbar := [Integers()!(g1/2)];
                    else 
                        gbar := [Integers()!((g1-1)/2),Integers()!((g1+1)/2)];
                    end if; 

                    Hasegawa_check := true; // check will remain true if criterion for being geom hyperelliptic is passed

                    for m2 in [m2 : m2 in HD | (m2 gt 1) and (m2 ne m1)] do
                        g2 := quot_genus(D,N,gens_to_identifier(D*N,{m1,m2}));
                        if not (g2 in gbar) then 
                            Hasegawa_check := false;
                            break;
                        end if;
                    end for;

                    if Hasegawa_check eq true then // If Hasegawa check required to be hyperelliptic goes through,
                                                    // we try to use finite field point counts to rule out X_0^D(N)/<w_{m1}> 
                                                    // being hyperelliptic

                        point_count_check := true; // check will remain true if criterion for being geom hyperelliptic is passed

                        Plist := PrimeDivisors(D*N);
                        m1_list := [Index(Plist,p) : p in PrimeDivisors(m1)];
                        for p in [p : p in PrimesUpTo(23) | not (p in Plist)] do // primes of good reduction for X_0^D(N)/<w_m1>. Increasing this to 100 seems to give no benefit
                            for r in [1,2] do
                                point_count := shiALpoints(p,r,D,N,[{},Seqset(m1_list)]);
                                if point_count gt 2*p^r+2 then 
                                    point_count_check := false;
                                    break;
                                end if;
                            end for;
                        end for; 

                        if point_count_check eq true then 
                            Append(~hypell_simple_quotient_candidates,[D,N,m1]);
                        end if; 
                    end if;
                end if;

            end for;
        end if; 

        // minimal genus of a quotient X_0^D(N)/<w_m> which we provably know is not hyperelliptic
        // by the above check
        non_hyperelliptic_AL_quotient_genera := [quot_genus(D,N,[1,m]) : m in HD | (m gt 1) and (not ([D,N,m] in hypell_simple_quotient_candidates))];
        if non_hyperelliptic_AL_quotient_genera ne [] then 
            g_2quot_nonhypell_min := Min(non_hyperelliptic_AL_quotient_genera);

            // Showing curves X_0^D(N) are not geometrically tetragonal via CS check with a simple AL quotient X_0^D(N)/<w_m>.
            // we need to avoid using quotients X_0^D(N)/<w_m> which are geometrically hyperelliptic for this check, 
            // as it could be the case that the tetragonal map factors through the map to X_0^D(N)/<w_m> in this case.
            if gtop gt 2*g_2quot_nonhypell_min+3 then
                Append(~not_geom_tetragonal_by_CS_2,pair);

            else
                // if pair has not been ruled out yet, we use further AL quotients. Now, since the degree of the AL
                // quotient map is at least 4 (the degree of the geometrically tetragonal map) and we have already
                // removed pairs with geometrically tetragonal maps to AL quotients, any AL quotient map of degree at least 4
                // would be independent of a geometrically tetragonal map (as the AL quotients are Galois) unless possibly
                // if they both factor through a simple AL quotient which then must be geometrically hyperelliptic.
                // We run a CS check using further AL quotients by checking that all simple AL quotients are non-hyperelliptic
                // using a separate CS check.
                for gens in AL_subgroups(D*N) do 
                    W := gens_to_identifier(D*N,gens);
                    order_W := #W; 
                    if order_W ge 4 then // already tried order 2 subgroups above
                        // CS check excluding possibility of having a geometrically tetragonal map and 
                        // the quotient map to X_0^D(N)/W
                        gW := quot_genus(D,N,W);
                        if gtop gt (order_W*gW + 3*(order_W-1)) then

                            // Ensuring the independence of the AL quotient by W and a hypothetical tetragonal map
                            // by showing they can't factor through a common hyperelliptic X_0^D(N)/<w_m>
                            ind_check := true;
                            for m1 in [m1 : m1 in W | (m1 gt 1) and (not ([D,N,m1] in hypell_simple_quotient_candidates))] do 
                                gm1 := quot_genus(D,N,[1,m1]);

                                // CS check for intermediate X_0^D(N)/<w_m1> factoring through tetragonal map 
                                if gm1 le ( Integers()!(order_W/2)*gW + Integers()!(order_W/2)-1 ) then 
                                    ind_check := false;
                                    break;
                                end if; 
                            end for;

                            if ind_check eq true then
                                Append(~not_geom_tetragonal_by_CS_4,pair);
                                Append(~not_geom_tetragonal_by_CS_4_with_W,[*pair,identifier_to_min_gens(pair[1]*pair[2],W)*]);
                                // print D, N, W;
                                // print genus(D,N);
                                // print quot_genus(D,N,W); 
                                break;
                            end if; 
                        end if; 
                    end if;
                end for; 
            end if;
        end if; 
    end if; 
end for; 


// Updating knowledge with newly initialized lists
remaining_geom_tetragonal_candidates := [pair : pair in tetragonal_candidates | not ((((pair in geom_tetragonal_by_AL_2) or (pair in geom_tetragonal_by_AL_4)) or (pair in not_geom_tetragonal_by_CS_2)) or (pair in not_geom_tetragonal_by_CS_4)) ];
Sort(~remaining_geom_tetragonal_candidates); 

remaining_tetragonal_candidates := [pair : pair in tetragonal_candidates | not  ((pair in not_geom_tetragonal_by_CS_2) or (pair in not_geom_tetragonal_by_CS_4))];
Sort(~remaining_tetragonal_candidates); 


geom_tetragonal_by_2_to_hyperelliptic := [];

// Sieving out pairs X_0^D(N) with N divisible by 4 for which X_0^D(N/2) is 
// geometrically (sub)hyperelliptic
for pair in remaining_geom_tetragonal_candidates do 
    if (pair[2] mod 4 eq 0) and (genus(pair[1],Integers()!(pair[2]/2)) le 2) then
        Append(~geom_tetragonal_by_2_to_hyperelliptic,pair); 
        Exclude(~remaining_geom_tetragonal_candidates,pair);
    end if;
end for; 


geom_tetragonal_by_polizzi := [];
geom_tetragonal_by_polizzi_with_info := [];
// Determining pairs X_0^D(N) which are found to be tetragonal by being a degree 2 cover of a 
// genus 3 hyperelliptic curve which is determined to be hyperelliptic via being a degree 2 
// cover of a genus 2 curve
for pair in remaining_geom_tetragonal_candidates do 
    D := pair[1];
    N := pair[2];
    HD := HallDivisors(D*N);
    for m1 in [m : m in HD | m gt 1] do
        if quot_genus(D,N,{1,m1}) eq 3 then 
            genus_2_quots := [m2 : m2 in HD | ((m2 ne 1) and (m2 ne m1)) and (quot_genus(D,N,gens_to_identifier(D*N,{m1,m2})) eq 2)];
            if genus_2_quots ne [] then 
                Append(~geom_tetragonal_by_polizzi,pair);
                Append(~geom_tetragonal_by_polizzi_with_info,[* pair, m1, genus_2_quots[1] *]);
                Exclude(~remaining_geom_tetragonal_candidates,pair);
                break;
            end if; 
        end if; 
    end for;
end for; 


not_geom_tetragonal_by_bihyperelliptic_lemma := [];
not_geom_tetragonal_by_bihyperelliptic_lemma_with_info := [];

for pair in remaining_geom_tetragonal_candidates do
    D := pair[1];
    N := pair[2];
    if (genus(D,N) ge 10) and (IsSquarefree(N)) then // in this case, we know a geom. tetragonal curve is geom. bi-hyperelliptic

        q_found := false; // set to true if we find a q such that the bound from the lemma succeeds

        for p in [p : p in PrimesUpTo(100) | not (p in PrimeDivisors(D*N))] do // primes up to 100 of good reduction for X_0^D(N)
            for i in [1..7] do
                point_count := shiALpoints(p,i,D,N,[{},{}]); // #X_0^D(N)(F_{p^i})
                if point_count gt 4*p^i+4 then // this implies X_0^D(N) is not geom. bi-hyperelliptic
                    q_found := true;
                    Append(~not_geom_tetragonal_by_bihyperelliptic_lemma,pair);
                    Append(~not_geom_tetragonal_by_bihyperelliptic_lemma_with_info,[D,N,p^i,point_count]);
                    Exclude(~remaining_tetragonal_candidates,pair);
                    Exclude(~remaining_geom_tetragonal_candidates,pair);
                    break;
                end if; 
            end for;

            if q_found eq true then 
                break;
            end if; 
        end for;
    end if;
end for; 



not_geom_tetragonal_by_bihyperelliptic_lemma_2 := [];

// If N is squarefree, we know all automorphisms are Atkin--Lehner, and g(X_0^D(N)) > 9, 
// then we know X_0^D(N) is geom. tetragonal iff it has a geom. bi-hyperelliptic Atkin-Lehner
// involution. Since all involutions of X_0^D(N)/<w_m> are Atkin--Lehner for any m||DN,
// we cannot We use point counts and Hasegawa's criterion to test each such involution. 

// first, we add some remaining pairs (D,N) with D*N even or X_0^D(N)^* of genus
// less than 2 for which the results of 
// Kontogeorgis--Rotger suffice to prove all automorphisms are Atkin--Lehner.
Append(~all_atkin_lehner_10k,[6,73]);
Append(~all_atkin_lehner_10k,[34,13]);
Append(~all_atkin_lehner_10k,[55,3]);
Append(~all_atkin_lehner_10k,[69,2]);
Append(~all_atkin_lehner_10k,[94,3]);
Append(~all_atkin_lehner_10k,[262,1]);
Append(~all_atkin_lehner_10k,[298,1]);
Append(~all_atkin_lehner_10k,[358,1]);
Append(~all_atkin_lehner_10k,[382,1]);

for pair in [pair : pair in remaining_geom_tetragonal_candidates | pair in all_atkin_lehner_10k] do 
    D := pair[1];
    N := pair[2];
    HD := [m : m in Hall_Divisors(D*N) | m gt 1];
    g := genus(D,N); 

    if g ge 10 then        
        Append(~not_geom_tetragonal_by_bihyperelliptic_lemma_2,pair);
        Exclude(~remaining_tetragonal_candidates,pair);
        Exclude(~remaining_geom_tetragonal_candidates,pair);
    end if; 
end for; 


not_tetragonal_by_point_counts := [];

// sieving out pairs based on finite field point counts, which give Q-gonality bounds
// (note: given the geometric checks above, we shouldn't get anything extra from this check
// except possibly for pairs of genus < 10).
for pair in remaining_tetragonal_candidates do 
    D := pair[1];
    N := pair[2]; 

    excluded_check := false;

    for p in [p : p in PrimesUpTo(100) | not (p in PrimeDivisors(D*N))] do
        for i in [1..7] do
            if shiALpoints(p,i,D,N,[{},{}]) gt 4*p^i+4 then // point count check to exclude being tetragonal over \Q
                excluded_check := true; 
                Append(~not_tetragonal_by_point_counts,pair);
                Exclude(~remaining_tetragonal_candidates,pair);
            end if; 
        end for;

        if excluded_check eq true then 
            break;
        end if;
    end for; 
end for; 


tetragonal_by_hyperelliptic := [];
// Sieving out pairs X_0^D(N) which are hyperelliptic over \Q. These are all
// hyperelliptic by an AL involution, and hence have an AL quotient map of degree 4
// to P^1_Q. 
for pair in remaining_tetragonal_candidates do 
    if pair in Q_gon_2 then
        Append(~tetragonal_by_hyperelliptic,pair); 
        Exclude(~remaining_tetragonal_candidates,pair);
    end if;
end for; 


tetragonal_by_bielliptic := [];
// Sieving out pairs X_0^D(N) which are bielliptic over \Q, and hence
// tetragonal over \Q
for pair in remaining_tetragonal_candidates do 
    if pair in Bielliptic_over_Q then
        Append(~tetragonal_by_bielliptic,pair); 
        Exclude(~remaining_tetragonal_candidates,pair);
    end if;
end for; 


tetragonal_by_2_to_hyperelliptic := [];
// Sieving out pairs X_0^D(N) with N divisible by 4 for which X_0^D(N/2) is hyperelliptic
// Here we find X_0^(15)(4) and X_0^(39)(4) are tetragonal over \Q. 
for pair in remaining_tetragonal_candidates do 
    if (pair[2] mod 4 eq 0) and ([pair[1],Integers()!(pair[2]/2)] in Q_gon_2) then
        Append(~tetragonal_by_2_to_hyperelliptic,pair); 
        Exclude(~remaining_tetragonal_candidates,pair);
    end if;
end for; 


// For pairs (D,N) for which we find that X_0^D(N) is found to be geometrically tetragonal
// via having an AL quotient X_0^D(N)/W with
//      * W of order 2 and X_0^D(N)/W genus at most 2, 
//      * W of order 4 and X_0^D(N)/W genus 0, or
//      * W of order 2, X_0^D(N)/W of genus 3 with a degree 2 (AL) cover to a genus 2 curve (Polizzi criterion)
// we work to show (D,N) is tetragonal over Q by showing there is W' <= W of order 2
// so that X_0^D(N)/W' has a rational CM point. 

load "cond_disc_list_allO.m";
load "shimura_curve_CM_locus.m";
class_num_1 := cond_disc_list_allO[1]; // class number 1 im quad orders
class_num_2 := cond_disc_list_allO[2]; // class number 2 im quad orders
class_num_4 := cond_disc_list_allO[4]; // class number 4 im quad orders

tetragonal_by_CM := [];
tetragonal_by_CM_with_info := [];

geom_tetragonal_by_AL := [pair : pair in tetragonal_candidates | ((pair in geom_tetragonal_by_AL_2) or (pair in geom_tetragonal_by_AL_4)) or (pair in geom_tetragonal_by_polizzi)];

// We consider pairs we have not yet handled which are known to be geometrically tetragonal
for pair in [pair : pair in geom_tetragonal_by_AL | (pair in remaining_tetragonal_candidates) and (IsSquarefree(pair[2]))] do
    D := pair[1];
    N := pair[2];

    // If a point on X_0^D(N)/<w_m> for some m=1 is rational, any preimage on X_0^D(N) is quadratic
    // (because D>1, so X_0^D(N) has no rational points),
    // so we compute the info of all quadratic CM points on X_0^D(N) to start. 
    quad_pts := [*[**],[**]*]; 
    
    for order in class_num_1 do
        pts := CM_points_XD0(D,order[1],order[2],N);

        if Type(pts) ne MonStgElt then 

            for pt in pts[2] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[2],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;
        end if; 
    end for; 

    for order in class_num_2 do
        pts := CM_points_XD0(D,order[1],order[2],N);

        if Type(pts) ne MonStgElt then

            for pt in pts[1] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[1],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;
        end if; 
    end for; 

    quad_image_info := [* *];
    rat_pts_m_values := [];
    HD := HallDivisors(D*N);

    // storing info of rational CM points on quotients X_0^D(N)/<w_m>
    for m in [m : m in HD | m gt 1] do

        m_points_info := [* *]; 

        for pt in quad_pts[1] do // GR06 Cor 5.14 (2)
            d_K := pt[1];
            f_R := pt[3];
            disc_R := f_R^2*d_K;
            m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f_R)));
            Q := m/m_r;

            D_R := 1;
            for pair in Factorization(D) do
                if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                    D_R := D_R*pair[1];
                end if;
            end for;

            N_star_R := 1;
            for pair in Factorization(N) do 
                if (KroneckerSymbol(disc_R,pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                    N_star_R := N_star_R*pair[1];
                end if;
            end for; 

            // Now we use GRO6 Cor. 5.14 (2) to determine rationality of image points
            // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
            // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
            // as if we actually have fixed points of these orders we have fixed points of 
            // order -3 or -4.
            if (Q eq 1)  then 
                Append(~m_points_info,[*d_K,pt[2],f_R,pt[4]*]);
            end if; 
        end for;

        for pt in quad_pts[2] do // GR06 Cor 5.14 (1)
            d_K := pt[1];
            f_R := pt[3];
            disc_R := f_R^2*d_K;
            m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f_R)));
            Q := m/m_r;

            D_R := 1;
            for pair in Factorization(D) do
                if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                    D_R := D_R*pair[1];
                end if;
            end for;

            N_star_R := 1;
            for pair in Factorization(N) do 
                if (KroneckerSymbol(disc_R,pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                    N_star_R := N_star_R*pair[1];
                end if;
            end for; 

            // Now we use GRO6 Cor. 5.14 (1) to determine rationality of image points
            // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
            // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
            // as if we actually have fixed points of these orders we have fixed points of 
            // order -3 or -4.
            if ((Q eq D_R*N_star_R) and (not (disc_R in [-12,-16,-27]))) then
                Append(~m_points_info,[*d_K,pt[2],f_R,pt[4]*]);
            end if; 
        end for;

        if m_points_info ne [* *] then
            Append(~rat_pts_m_values,m);
            Append(~quad_image_info,[*m,m_points_info*]);
        end if;
    end for;

    // If at least one quotient X_0^D(N)/<w_m> has a rational point,
    // we check quotients to try to guarantee X_0^D(N) is tetragonal over Q
    if rat_pts_m_values ne [] then 

        for gens in AL_subgroups(D*N) do 

            W := gens_to_identifier(D*N,gens);

            // We consider quotients X_0^D(N)/<w_m> with rational points through which
            // the quotient by W factors
            m_with_rat_pts_in_W := [m : m in W | m in rat_pts_m_values];

            if m_with_rat_pts_in_W ne [] then

                order_W := #W; 

                if order_W eq 2 then 
                    // Witnessing tetragonal by a (sub)hyperelliptic X_0^D(N)/<w_m>
                    if quot_genus(D,N,W) le 2 then 
                        Append(~tetragonal_by_CM,pair);
                        Append(~tetragonal_by_CM_with_info,[*pair,W,[list : list in quad_image_info | list[1] in m_with_rat_pts_in_W]*]);
                        Exclude(~remaining_tetragonal_candidates,pair);
                        break;

                    // Witnessing tetragonal by X_0^D(N)/<w_m> which is hyperelliptic
                    // based on having a rational point, being genus 3, and being a degree 2 
                    // cover of a further AL quotient of genus 2  
                    elif quot_genus(D,N,W) eq 3 then 
                        m1 := W[2]; 
                        genus_2_quots := [m2 : m2 in HD | ((m2 ne 1) and (m2 ne m1)) and (quot_genus(D,N,gens_to_identifier(D*N,{m1,m2})) eq 2)];
                        if genus_2_quots ne [] then 
                            Append(~tetragonal_by_CM,pair);
                            Append(~tetragonal_by_CM_with_info,[*pair,W,[list : list in quad_image_info | list[1] in m_with_rat_pts_in_W]*]);
                            Exclude(~remaining_tetragonal_candidates,pair);
                            break;
                        end if; 
                    end if;


                // Witnessing tetragonal by a X_0^D(N)/<w_{m_1},w_{m_2}> isomorphic to P^1 over Q
                elif order_W eq 4 then 
                    if quot_genus(D,N,W) eq 0 then 
                        Append(~tetragonal_by_CM,pair);
                        Append(~tetragonal_by_CM_with_info,[*pair,W,[list : list in quad_image_info | list[1] in m_with_rat_pts_in_W]*]);
                        Exclude(~remaining_tetragonal_candidates,pair);
                        break;
                    end if;
                end if; 
            end if; 
        end for;
    end if;
end for; 


// for pairs (D,N) which have a genus 0 quotient X_0^D(N)/W with |W| = 4, for which the 
// check for rational points on proper intermediate quotients did not succeed, 
// we check for degree 4 points which are not inert under the quotient by each non-trivial 
// involution w in W (and thus have rational image on the quotient by W). 

// Note: it seems this does not get us anything additional. 

tetragonal_by_quartic_CM := [];
tetragonal_by_quartic_CM_with_info := [];

for pair in [pair : pair in geom_tetragonal_by_AL | not (pair in tetragonal_by_CM)] do 
    D := pair[1];
    N := pair[2];

    found_rat := false;

    for W in AL_subgroups(D*N) do 
        id := gens_to_identifier(D*N,W);
        if #id eq 4 then 
            gW := quot_genus(D,N,id);
            if gW eq 0 then 

                // now we check quartic CM points on X_0^D(N)
                // to try to prove one has image on X_0^D(N)/W which is rational

                // first we list data on the quartic points
                quartic_pts := [* [**], [**] *]; 
    
                for order in class_num_1 do
                    pts := CM_points_XD0(D,order[1],order[2],N);

                    if Type(pts) ne MonStgElt then 

                        for pt in pts[2] do 
                            if pt[3] eq 4 then 
                                Append(~quartic_pts[2],[order[2],order[1],pt[1],pt[4]]);
                            end if;
                        end for;
                    end if; 
                end for; 

                for order in class_num_2 do
                    pts := CM_points_XD0(D,order[1],order[2],N);

                    if Type(pts) ne MonStgElt then

                        for pt in pts[1] do 
                            if pt[3] eq 4 then 
                                Append(~quartic_pts[1],[order[2],order[1],pt[1],pt[4]]);
                            end if;
                        end for;

                        for pt in pts[2] do 
                            if pt[3] eq 4 then 
                                Append(~quartic_pts[2],[order[2],order[1],pt[1],pt[4]]);
                            end if;
                        end for;

                    end if; 
                end for; 

                for order in class_num_4 do
                    pts := CM_points_XD0(D,order[1],order[2],N);

                    if Type(pts) ne MonStgElt then

                        for pt in pts[1] do 
                            if pt[3] eq 4 then 
                                Append(~quartic_pts[1],[order[2],order[1],pt[1],pt[4]]);
                            end if;
                        end for;
                    end if; 
                end for; 

                // now we check for rationality of the image on X_0^D(N)/W of each quartic point
                for pt in quad_pts[1] do // GR06 Cor 5.14 (2)
                    split_check := true; // will remain true if pt is split under each nontrivial w_m in W 
                    
                    for m in [m : m in id | m gt 1] do
                        d_K := pt[1];
                        f_R := pt[3];
                        disc_R := f_R^2*d_K;
                        m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f_R)));
                        Q := m/m_r;

                        D_R := 1;
                        for pair in Factorization(D) do
                            if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                                D_R := D_R*pair[1];
                            end if;
                        end for;

                        N_star_R := 1;
                        for pair in Factorization(N) do 
                            if (KroneckerSymbol(disc_R,pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                                N_star_R := N_star_R*pair[1];
                            end if;
                        end for; 

                        // Now we use GRO6 Cor. 5.14 (2) to determine rationality of image points
                        // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
                        // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
                        // as if we actually have fixed points of these orders we have fixed points of 
                        // order -3 or -4.
                        if (Q ne 1)  then 
                            split_check := false;
                            break; 
                        end if; 
                    end for;

                    if split_check eq true then 
                        found_rat := true; 
                        Append(~tetragonal_by_quartic_CM,pair);
                        Append(~tetragonal_by_quartic_CM_with_info,[*D,N,W,disc_R*]);
                        break;
                    end if; 

                end for; 

                if found_rat eq true then 
                    break;
                end if; 

                for pt in quad_pts[2] do // GR06 Cor 5.14 (1)

                    split_check := true; // will remain true if pt is split under each nontrivial w_m in W 
                    
                    for m in [m : m in id | m gt 1] do
                        d_K := pt[1];
                        f_R := pt[3];
                        disc_R := f_R^2*d_K;
                        m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f_R)));
                        Q := m/m_r;

                        D_R := 1;
                        for pair in Factorization(D) do
                            if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                                D_R := D_R*pair[1];
                            end if;
                        end for;

                        N_star_R := 1;
                        for pair in Factorization(N) do 
                            if (KroneckerSymbol(disc_R,pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                                N_star_R := N_star_R*pair[1];
                            end if;
                        end for; 

                        // Now we use GRO6 Cor. 5.14 (1) to determine rationality of image points
                        // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
                        // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
                        // as if we actually have fixed points of these orders we have fixed points of 
                        // order -3 or -4.
                        if ((Q ne D_R*N_star_R) or ((disc_R in [-12,-16,-27]))) then
                            split_check := false;
                            break; 
                        end if; 
                    end for;

                    if split_check eq true then 
                        Append(~tetragonal_by_quartic_CM,pair);
                        Append(~tetragonal_by_quartic_CM_with_info,[*D,N,W,disc_R*]);
                    end if; 

                end for; 

                if found_rat eq true then 
                    break;
                end if; 

            end if;
        end if;
    end for;
end for; 
        
               
// (10,9) is tetragonal over \Q by Prop. 4.27 of Nualart-Riera's thesis. 
Exclude(~remaining_tetragonal_candidates,[10,9]);


// SetOutputFile("remaining_geom_tetragonal_candidates.m");
// print "remaining_geom_tetragonal_candidates := ";
// remaining_geom_tetragonal_candidates;
// print ";"; 
// UnsetOutputFile(); 

// SetOutputFile("remaining_tetragonal_candidates.m");
// print "remaining_tetragonal_candidates := ";
// remaining_tetragonal_candidates;
// print ";"; 
// UnsetOutputFile(); 
   


///////////////////////////////////////////////
///////////////////////////////////////////////
// printing tables for LaTeX
///////////////////////////////////////////////
///////////////////////////////////////////////


// X_0^D(N) geometrically tetragonal via X_0^D(N)/<w_m> having genus <= 2

// SetOutputFile("table_geom_tetragonal_by_AL_2.m");
// for i in [1..66] do 
//     for j in [1..2] do
//         print "$ (";
//         pair := geom_tetragonal_by_AL_2[2*(i-1)+j];
//         D := pair[1];
//         N := pair[2];
//         HD := HallDivisors(D*N);
//         print D, ",", N, ")$ & $";

//         gtop := genus(D,N);
//         g_2quot_min := gtop;
//         m_min := 1;
//         for m in HD do 
//             g := quot_genus(D,N,[1,m]);
//             if g lt g_2quot_min then 
//                 g_2quot_min := g;
//                 m_min := m;
//             end if;
//         end for; 
        
//         print m_min, "$ & $", g_2quot_min, "$";

//         if j eq 2 then 
//             print "\\ \hline";
//         else 
//             print " & "; 
//         end if;
//     end for;
// end for; 

// // final row, 1 entry
// pair := geom_tetragonal_by_AL_2[133];

// D := pair[1];
// N := pair[2];
// HD := HallDivisors(D*N);
// print "$ (", D, ",", N, ")$ & $";

// gtop := genus(D,N);
// g_2quot_min := gtop;
// m_min := 1;
// for m in HD do 
//     g := quot_genus(D,N,[1,m]);
//     if g lt g_2quot_min then 
//         g_2quot_min := g;
//         m_min := m;
//     end if;
// end for; 

// print m_min, "$ & $", g_2quot_min, "$ & & & \\ \hline"; 
// UnsetOutputFile();



// X_0^D(N) geometrically tetragonal via some X_0^D(N)/<w_{m_1},w_{m_2}> having genus 0

    // SetOutputFile("table_geom_tetragonal_by_AL_4.m");

    // for i in [1..8] do 
    //     for j in [1..3] do
    //         print "$ (";
    //         pair := geom_tetragonal_by_AL_4[3*(i-1)+j];
    //         D := pair[1];
    //         N := pair[2];
    //         HD := HallDivisors(D*N);
    //         print D, ",", N, ")$ & $";

    //         found := false;
    //         for m1 in [m : m in HD | (m gt 1) and (m lt Max(HD))] do 
    //             for m2 in [m : m in HD | (m gt m1)] do
    //                 g_quot := quot_genus(D,N,gens_to_identifier(D*N,{m1,m2}));
    //                 if g_quot eq 0 then 
    //                     print m1, ",", m2, "$";
    //                     found := true;
    //                     break; 
    //                 end if; 
    //             end for;
    //             if found eq true then
    //                 break;
    //             end if; 
    //         end for;

    //         if j eq 3 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 
    // UnsetOutputFile();



// X_0^D(N) not geometrically tetragonal via a CS arugment involving an AL quotient
// X_0^D(N)/<w_m> which we know is not geometrically hyperelliptic. 

    // SetOutputFile("table_not_geom_tetragonal_by_CS_2.m");

    // for i in [1..107] do 
    //     for j in [1..3] do
            
    //         pair := not_geom_tetragonal_by_CS_2[3*(i-1)+j];
    //         D := pair[1];
    //         N := pair[2];
    //         HD := HallDivisors(D*N);
    //         print "$ (";
    //         print D, ",", N, ")$ & $";

    //         gtop := genus(D,N);
    //         g_2quot_min := gtop;
    //         m_min := 1;
    //         for m in [m : m in HD | not ([D,N,m] in hypell_simple_quotient_candidates)] do 
    //             g := quot_genus(D,N,[1,m]);
    //             if g lt g_2quot_min then 
    //                 g_2quot_min := g;
    //                 m_min := m;
    //             end if;
    //         end for; 
            
    //         print m_min, "$ & $", gtop, "$ & $", g_2quot_min, "$";

    //         if j eq 3 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 

    // // final row, 1 entry 
    // pair := not_geom_tetragonal_by_CS_2[322];
    // D := pair[1];
    // N := pair[2];
    // HD := HallDivisors(D*N);
    // print "$ (";
    // print D, ",", N, ")$ & $";

    // gtop := genus(D,N);
    // g_2quot_min := gtop;
    // m_min := 1;
    // for m in [m : m in HD | not ([D,N,m] in hypell_simple_quotient_candidates)] do 
    //     g := quot_genus(D,N,[1,m]);
    //     if g lt g_2quot_min then 
    //         g_2quot_min := g;
    //         m_min := m;
    //     end if;
    // end for; 

    // print m_min, "$ & $", gtop, "$ & $", g_2quot_min, "$ & & & & & & & & \\ \hline";
    // UnsetOutputFile();



// X_0^D(N) tetragonal over Q via rational CM points

    // SetOutputFile("table_tetragonal_by_CM.m");

    // for i in [1..27] do 
    //     for j in [1..3] do
            
    //         info := tetragonal_by_CM_with_info[3*(i-1)+j];
    //         pair := info[1];
    //         D := pair[1];
    //         N := pair[2];
    //         print "$ (";
    //         print D, ",", N, ")$ & $";

    //         m := info[3][1][1];
    //         Delta := info[3][1][2][1][1]; // first CM discriminant in list of rational pts info
            
    //         print m, "$ & $", Delta, "$";

    //         if j eq 3 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 

    // // final row, 1st entry
    // info := tetragonal_by_CM_with_info[82];
    // pair := info[1];
    // D := pair[1];
    // N := pair[2];
    // print "$ (";
    // print D, ",", N, ")$ & $";
    // m := info[3][1][1];
    // Delta := info[3][1][2][1][1]; // first CM discriminant in list of rational pts info
    // print m, "$ & $", Delta, "$ & ";

    // // final row, 2nd entry
    // info := tetragonal_by_CM_with_info[83];
    // pair := info[1];
    // D := pair[1];
    // N := pair[2];
    // print "$ (";
    // print D, ",", N, ")$ & $";
    // m := info[3][1][1];
    // Delta := info[3][1][2][1][1]; // first CM discriminant in list of rational pts info
    // print m, "$ & $", Delta, "$ & & & \\ \hline";

    // UnsetOutputFile();



// X_0^D(N) not tetragonal over Q via finite field point counts

    // SetOutputFile("table_not_tetragonal_by_point_counts.m");

    // for i in [1..16] do 
    //     for j in [1..4] do
    //         print "$ (";
    //         pair := not_tetragonal_by_point_counts[4*(i-1)+j];
    //         D := pair[1];
    //         N := pair[2];
    //         print D, ",", N, ")$";

    //         if j eq 4 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 

    // // final row, 1 entry
    // pair := not_geom_tetragonal_by_CS_2[65];

    // D := pair[1];
    // N := pair[2];
    // print "$ (";
    // print D, ",", N, ")$ & & & \\ \hline";

    // UnsetOutputFile();


// X_0^D(N) not tetragonal over Q via bihyperelliptic lemma

    // SetOutputFile("table_not_tetragonal_by_bihyperelliptic_lemma.m");

    // for i in [1..5] do 
    //     for j in [1..2] do
    //         print "$ (";
    //         curve_info := not_geom_tetragonal_by_bihyperelliptic_lemma_with_info[2*(i-1)+j];
    //         D := curve_info[1];
    //         N := curve_info[2];
    //         q := curve_info[3];
    //         count := curve_info[4];
    //         print D, ",", N, ")$ & ", q, " & ", count;

    //         if j eq 2 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 

    // // final row, 1 entry
    // curve_info := not_geom_tetragonal_by_bihyperelliptic_lemma_with_info[11];
    // D := curve_info[1];
    // N := curve_info[2];
    // q := curve_info[3];
    // count := curve_info[4];
    // print "$ (";
    // print D, ",", N, ")$ & ", q, " & ", count, " & & & \\ \hline";
    // UnsetOutputFile();


// Remaining geometrically tetragonal candidates

    // SetOutputFile("table_remaining_geom_tetragonal_candidates.m");

    // for i in [1..3] do 
    //     for j in [1..3] do
    //         pair := remaining_geom_tetragonal_candidates[3*(i-1)+j];
    //         D := pair[1];
    //         N := pair[2];
    //         g := genus(D,N); 
    //         print "$ (";
    //         print D, ",", N, ")$ & $", g, "$";

    //         if j eq 3 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 

    // // final row, 1 entry 
    // curve_info := remaining_geom_tetragonal_candidates[10];
    // D := pair[1];
    // N := pair[2];
    // g := genus(D,N); 
    // print "$ (";
    // print D, ",", N, ")$ & $ ", g, "$ & & & & \\ \hline";

    // UnsetOutputFile();


// Remaining tetragonal candidates

    // remaining_tetragonal_candidates_only := [pair : pair in remaining_tetragonal_candidates | not (pair in remaining_geom_tetragonal_candidates)];
    // SetOutputFile("table_remaining_tetragonal_candidates.m");

    // for i in [1..6] do 
    //     for j in [1..3] do
    //         pair := remaining_tetragonal_candidates_only[3*(i-1)+j];
    //         D := pair[1];
    //         N := pair[2];
    //         g := genus(D,N); 
    //         print "$ (";
    //         print D, ",", N, ")$ & $", g, "$";

    //         if j eq 3 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 

    // // final row, 1 entry 
    // pair := remaining_tetragonal_candidates_only[19];
    // D := pair[1];
    // N := pair[2];
    // g := genus(D,N); 
    // print "$ (";
    // print D, ",", N, ")$ & $", g, "$ & & & & \\ \hline";

    // UnsetOutputFile();

 

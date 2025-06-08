// gens_to_identifier: given DN an integer and gens a set of Hall divisors of DN,
// returns the identifier for W = <w_m | m in gens>, by which we mean the ordered sequence of
// Hall divisors m so that {w_m | m in identifier} is the full set of nontrivial elements of W
gens_to_identifier := function(DN,gens)

     G := Setseq(gens);
     prods := Subsets(gens,2);
     while #prods gt 0 do
    	newprod := [];
    	for p in prods do
    	    A := (&*p) div GCD(p)^2;
    	    if (A notin G) and (A notin newprod) then
              	Append(~newprod,A);
    	    end if;
    	end for;

    	if #newprod gt 0 then
    	    prods := {{a,b} : a in G, b in newprod} join Subsets(Seqset(newprod),2);
    	    G := G cat newprod;
    	else
    	    prods := {};
    	end if;

     end while;

     // if 1 was not included in the original generating set, add it to the identifier G
     if not (1 in G) then 
          Append(~G,1);
     end if;

     Sort(~G); 

     return G;
end function;



// Given a set gens of generators for a subgroup W of W_0(D,N), 
// checks whether it is the identifier for W (without computing the identifier itself)
is_identifier := function(DN,gens)
     G := gens;

     if not (1 in G) then 
          return false;
     end if;

     prods := Subsets(gens,2);

     for p in prods do
         A := (&*p) div GCD(p)^2;
         if (A notin G) then
               return false;  
         end if;
     end for;

     return true; 
end function;



// given the identifier [m : w_m in W] of a subgroup W of W_0(D,N),
// return a minimal size set min_gens so that <w_m : m in min_gens> = W
// (of course, such a minimal length set is non unique; we output one such set)
identifier_to_min_gens := function(DN, identifier)
     subgroup_size := #identifier;
     min_gens_size := Integers()!Log(2,subgroup_size);
     for gen_set in Subsets(Seqset(identifier),min_gens_size) do
          if gens_to_identifier(DN,gen_set) eq identifier then 
               return gen_set;
          end if;
     end for;
end function; 



// given a positive integer n, returns the sequence of divisors d | n such that GCD(d,n/d) = 1.
HallDivisors := function(n) 
    assert n ge 1;
    return {d : d in Divisors(n) | GCD(d,Integers()!(n/d)) eq 1};
end function;



// given two identifiers or min generating sequences, sort them first according to length and then by lexicographic ordering
identifier_comparison := function(I1,I2)

     if I1 eq I2 then 
          return 0;

     else 
          s1 := #I1;
          s2 := #I2;

          if s1 ne s2 then
               return s1-s2;

          else
               if Type(I1) eq SetEnum then // if given min generating sets, convert to sequences to compare
                    I1 := Setseq(I1);
                    I2 := Setseq(I2);
               end if;

               for i in [1..s1] do
                    if I1[i] ne I2[i] then
                         return I1[i] - I2[i];
                    end if;
               end for;
          end if;
     end if;
end function; 



// given an integer DN, returns the ordered sequence containing one minimal generating set
// for each of the Atkin--Lehner quotients of X_0^D(N) 
// (this sequence only depends on the product DN)
AL_subgroups := function(DN)

     omega := #PrimeDivisors(DN); // size of minimal generating set of W_0(D,N), i.e., log_2(#W_0(D,N))
     HD := HallDivisors(DN); // set of Hall divisors of DN
     Subgroups_Set := {{1}}; // initializing set of min generating sets with that of the trivial quotient

     for j in [2..omega] do 
          for gens in Subsets(HD,j) do
               Include(~Subgroups_Set,identifier_to_min_gens(DN,gens_to_identifier(DN,gens)));
          end for;
     end for; 

     Subgroups_Seq := Setseq(Subgroups_Set);
     Sort(~Subgroups_Seq,identifier_comparison);
     return Subgroups_Seq; 

end function;



load "quot_genus.m";

// all_quotients_genera: given D, N, prints list of AL quotients with their genera
all_quotients_genera := procedure(D,N)
     for subgroup in AL_subgroups(D*N) do 
          id := gens_to_identifier(D*N,subgroup);
          print subgroup, id, quot_genus(D,N,id);
     end for;
end procedure;





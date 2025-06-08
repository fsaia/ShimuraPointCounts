// Let (D,N) be a pair consisting of a quaternion discriminant D>1 and a positive
// integer N coprime to D. If DN > 77416, then we known X_0^D(N) is not tetragonal. 
// For such pairs up to this bound, we now use explicit genus computations to
// check the inequality

// (975/8192)*(g(X_0^D(N)))-1) > 4.

// If this is satisfied, then X_0^D(N) is not geometrically of gonality at most 4. Otherwise, we 
// call (D,N) a "tetragonal_top_candidate" if g(X_0^D(N)) >= 2. 

// creating sequence of pairs (D,N) with the conditions mentioned above and with DN <= 77416
initial_DN_bound := 77416; 

pairs_up_to_bound := [];

for D in [D : D in [6..initial_DN_bound] | MoebiusMu(D) eq 1] do 
    for N in [N : N in [1..Floor(initial_DN_bound/D)] | GCD(D,N) eq 1] do
        Append(~pairs_up_to_bound,[D,N]);
    end for;
end for; 



// loading quot_genus.m, which contains the genus(D,N) function for the genus of X_0^D(N)
load "quot_genus.m";

// loading AL_identifiers.m, which contains code for working with unique identifiers 
// for each subgroup of the full Atkin--Lehner group W_0(D,N) of X_0^D(N). 
load "AL_identifiers.m";

// loading known_gonalities lists
load "known_gonalities.m";


// generating list of tetragonal candidates as defined above

tetragonal_candidates := []; // initializing sequence of tetragonal candidates

for pair in pairs_up_to_bound do 
    D := pair[1];
    N := pair[2]; 

    if ( (975/8192)*(genus(D,N)-1) le 4) then  
        if ((not (pair in genus_0)) and (not (pair in genus_1))) then
            Append(~tetragonal_candidates,pair); 
        end if; 
    end if; 
end for;


// SetOutputFile("tetragonal_candidates.m");
// print "tetragonal_candidates := ";
// tetragonal_candidates; 
// print ";";
// UnsetOutputFile();
   





 

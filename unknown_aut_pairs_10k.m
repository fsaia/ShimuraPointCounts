// List of all 112 of the 4830 pairs (D,N) with D>1 an indefinite quaternion discriminant, N
// a positive integer which is squarefree and coprime to D, D*N odd, and DN < 10000 for which
// we have not yet determined whether X_0^D(N)^* has a non-trivial involution.

unknown_aut_pairs_10k :=  [
    [ 21, 29 ],
    [ 21, 145 ],
    [ 21, 305 ],
    [ 33, 85 ],
    [ 33, 101 ],
    [ 55, 13 ],
    [ 69, 17 ],
    [ 77, 17 ],
    [ 93, 5 ],
    [ 115, 13 ],
    [ 129, 5 ],
    [ 133, 1 ],
    [ 133, 17 ],
    [ 145, 1 ],
    [ 177, 5 ],
    [ 205, 1 ],
    [ 265, 1 ],
    [ 321, 5 ],
    [ 341, 1 ],
    [ 437, 1 ],
    [ 445, 1 ],
    [ 453, 5 ],
    [ 497, 1 ],
    [ 517, 1 ],
    [ 537, 5 ],
    [ 583, 1 ],
    [ 989, 1 ],
    [ 1981, 5 ],
    [ 5221, 1 ],
    [ 5357, 1 ],
    [ 5539, 1 ],
    [ 5773, 1 ],
    [ 6049, 1 ],
    [ 6109, 1 ],
    [ 6433, 1 ],
    [ 6509, 1 ],
    [ 6583, 1 ],
    [ 6901, 1 ],
    [ 6913, 1 ],
    [ 6937, 1 ],
    [ 7093, 1 ],
    [ 7097, 1 ],
    [ 7117, 1 ],
    [ 7171, 1 ],
    [ 7181, 1 ],
    [ 7183, 1 ],
    [ 7291, 1 ],
    [ 7441, 1 ],
    [ 7531, 1 ],
    [ 7633, 1 ],
    [ 7781, 1 ],
    [ 7795, 1 ],
    [ 7849, 1 ],
    [ 7961, 1 ],
    [ 8057, 1 ],
    [ 8119, 1 ],
    [ 8137, 1 ],
    [ 8141, 1 ],
    [ 8143, 1 ],
    [ 8149, 1 ],
    [ 8153, 1 ],
    [ 8197, 1 ],
    [ 8347, 1 ],
    [ 8401, 1 ],
    [ 8413, 1 ],
    [ 8453, 1 ],
    [ 8509, 1 ],
    [ 8605, 1 ],
    [ 8617, 1 ],
    [ 8653, 1 ],
    [ 8767, 1 ],
    [ 8797, 1 ],
    [ 8809, 1 ],
    [ 8813, 1 ],
    [ 8857, 1 ],
    [ 8953, 1 ],
    [ 8981, 1 ],
    [ 9017, 1 ],
    [ 9019, 1 ],
    [ 9037, 1 ],
    [ 9053, 1 ],
    [ 9121, 1 ],
    [ 9193, 1 ],
    [ 9233, 1 ],
    [ 9235, 1 ],
    [ 9259, 1 ],
    [ 9289, 1 ],
    [ 9353, 1 ],
    [ 9379, 1 ],
    [ 9449, 1 ],
    [ 9469, 1 ],
    [ 9481, 1 ],
    [ 9493, 1 ],
    [ 9505, 1 ],
    [ 9523, 1 ],
    [ 9553, 1 ],
    [ 9557, 1 ],
    [ 9571, 1 ],
    [ 9637, 1 ],
    [ 9655, 1 ],
    [ 9713, 1 ],
    [ 9727, 1 ],
    [ 9793, 1 ],
    [ 9799, 1 ],
    [ 9853, 1 ],
    [ 9865, 1 ],
    [ 9913, 1 ],
    [ 9917, 1 ],
    [ 9961, 1 ],
    [ 9977, 1 ],
    [ 9979, 1 ],
    [ 9989, 1 ]
]
;


// Print table for paper
    // load "quot_genus.m";

    // // Hall_Divisors : given positive integer N, returns sequence of all Hall Divisors d || N. 
    // HallDivisors := function(N)
    //     assert N ge 1;
    //     return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1];
    // end function;

    // SetOutputFile("table_unknown_aut.m");

    // for i in [1..56] do 
    //     for j in [1..2] do
            
    //         pair := unknown_aut_pairs_10k[2*(i-1)+j];
    //         D := pair[1];
    //         N := pair[2];
    //         g := genus(D,N); 
    //         gstar := quot_genus(D,N,HallDivisors(D*N)); 

    //         print "$ (", D, ",", N, ")$ & $", g, "$ & $", gstar, "$";

    //         if j eq 2 then 
    //             print "\\ \hline";
    //         else 
    //             print " & "; 
    //         end if;
    //     end for;
    // end for; 

    // UnsetOutputFile();



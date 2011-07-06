-- Macaulay2 function for computing the graph S_n(d), that is: the vertices 
-- are all monomials of degree d in n variables; two monomials j,k are 
-- adjacent if lcm(j,k) = d + 1
--
-- This is adapted from the algorithm for computing the spreading/covering 
-- numbers ported from CoCoA.
--
-- v1.0
-- Ben Babcock <bababcoc@lakeheadu.ca>
------------------------------------------------------------------------------

needsPackage "EdgeIdeals"

monomialGraph = (n,d) -> (
	k := binomial(d + n - 1, n - 1);
	S := QQ[x_1..x_n];
	T := QQ[z_1..z_k];

	-- In the ring S, first determine all monomials of degree d. Second,
	-- determine which pair of monomials have a LCM of degree d+1
	monoS := (monomialIdeal(gens S))^d;
	Sd := flatten entries gens monoS;
	Pairs := {};
	for i from 1 to k do (
		for j from (i + 1) to k do (
			m := lcm(Sd#(i - 1), Sd#(j - 1));
			degm := first degree m;
			if degm == d + 1 then Pairs = append(Pairs,{z_i, z_j});
		);
	);

	-- Build the graph of S_n(d) from the list of monomial pairs
	return(graph(T,Pairs));
)
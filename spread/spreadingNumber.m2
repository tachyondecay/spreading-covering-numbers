-- Macaulay2 function for computing the spreading number
-- v1.0
--
-- Ported to Macaulay2 by Ben Babcock <bababcoc@lakeheadu.ca>
-- Based on original CoCoA algorithm by E. Carlini, H. T. Ha, and A. Van Tuyl.
------------------------------------------------------------------------------

spreadingNumber = (n,d) -> (
	if n == 1 or d == 1 then return 1;
	if d == 2 then return n;

	k := binomial(d + n - 1, n - 1);
	S := QQ[x_1..x_n];
	T := QQ[z_1..z_k];

	-- In the ring S, first determine all monomials of degree d. Second,
	-- determine which pair of monomials have a LCM of degree d+1
	monoS := (monomialIdeal(gens S))^d;
	Sd := flatten entries gens monoS;
	idealGens := {};
	for i from 1 to k do (
		for j from (i + 1) to k do (
			m := lcm(Sd#(i - 1), Sd#(j - 1));
			degm := first degree m;
			if degm == d + 1 then idealGens = append(idealGens, z_i*z_j);
		);
	);

	-- Construct the Stanley-Reisner ring and compute its dimension
	ISimpComp := monomialIdeal idealGens;
	return(dim(T/ISimpComp));
)
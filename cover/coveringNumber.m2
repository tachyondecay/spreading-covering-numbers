-- Macaulay2 function for computing the covering number, that is, the 
-- minimum number of monomials of degree d required to cover the monomials of 
-- degree d + 1.
--
-- v1.0
--
-- Ported to Macaulay2 by Ben Babcock <bababcoc@lakeheadu.ca>
-- Based on original CoCoA algorithm by E. Carlini, H. T. Ha, and A. Van Tuyl.
------------------------------------------------------------------------------

coveringNumber = (n,d) -> (
	if n == 1 then return 1;
	if d == 1 then return n;

	k := binomial(d + n - 1, n - 1);
	S := QQ[x_1..x_n];
	T := QQ[z_1..z_(k - n)];

	Ad := flatten entries gens((monomialIdeal(gens S))^d);
	AdPlus1 := flatten entries gens((monomialIdeal(gens S))^(d + 1));

	Powers := for i from 1 to n list x_i^d;
	Powers2 := {};
	for i from 1 to n do (
		for j from 0 to (#Powers - 1) do (
			Powers2 = append(Powers2, x_i*Powers#j);
		);
	);

	AdPrime := select(Ad, i -> not member(i,Powers));
	AdPlus1Prime := select(AdPlus1, i -> not member(i, Powers2));

	W := for i from 0 to (#AdPrime - 1) list (Powers | drop(AdPrime,{i,i}));

	Igens := {};
	for i from 0 to (#AdPlus1Prime - 1) do (
		m := AdPlus1Prime#i;
		mQuotients := for j from 1 to n list (if gcd(m, x_j) == 1 then continue; m//x_j);
		Igens = append(Igens, 
				product apply(mQuotients, m -> (
					product for i from 0 to (#W - 1) list (if member(m, W#i) then continue; z_(i+1))
				))
			);
	);

	ISimpComp := monomialIdeal Igens;
	return(k - dim(T/ISimpComp));
);
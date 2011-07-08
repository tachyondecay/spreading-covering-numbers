-- Macaulay2 function to compute an upper bound of the spreading number
--
-- Ben Babcock <bababcoc@lakeheadu.ca
-------------------------------------------------------------------------------

needsPackage "EdgeIdeals";

isClique = method();
isClique(Graph, List) := (G,c) -> (
	for i when i < #c do (
		for j from i + 1 to (#c - 1) do (
			if not isEdge(G, {c#i, c#j}) then return false;
		);
	);
	return true;
);


spreadingNumberBound = (n,d) -> (
	if n == 1 or d == 1 then return 1;
	if d == 2 then return n;

	k := binomial(d + n - 1, n - 1);
	S := QQ[x_1..x_n];
	T := QQ[z_1..z_k];

	-- In the ring S, first determine all monomials of degree d. Second,
	-- determine which pair of monomials have a LCM of degree d + 1
	Sd := flatten entries gens((monomialIdeal(gens S))^d);
	Pairs := {};
	legend := {};
	for i from 1 to k do (
		legend = append(legend, {z_i, Sd#(i - 1)});

		for j from (i + 1) to k do (
			m := lcm(Sd#(i - 1), Sd#(j-1));
			degm := first degree m;
			if degm == d + 1 then Pairs = append(Pairs,{z_i,z_j});
		);
	);

	-- This table will match up generators of T with monomials of S_n(d)
	legend = hashTable legend;
	inverseLegend := applyPairs(legend, (p,q) -> (q,p));

	-- Construct the graph S_n(d)
	G := graph(T, Pairs);

	-- Partition the vertices of G by the transposition (12...n-1)
	remainingVertices := vertices G;
	parts := while #remainingVertices > 0 list (
		currentVertex := first remainingVertices;
		vClass := {currentVertex};
		while(true) do (
			f := factor legend#(currentVertex);
			m := 1;

			for k when k < #f do (
				i := index f#k#0;
				if i < (n - 1) then i = (i + 1) % (n - 1);
				m = m*(x_(i + 1)^(f#k#1));
			);
			m = inverseLegend#m;
			currentVertex = m;
			if m == first remainingVertices then (
				if #vClass == 1 then vClass = append(vClass, m);
				break;
			);
			vClass = append(vClass, m);
		);
		remainingVertices = toList(set(remainingVertices) - set(vClass));
		vClass
	);

	numPartsCliques := 0;
	parts = for i when i < #parts list (
		if #(unique parts#i) == 1 then continue
		else (
			if isClique(G, parts#i) then numPartsCliques = numPartsCliques + 1;
			sum parts#i
		)
	);
	print numPartsCliques;
	print parts;
	edgeIdealGens := apply(edges G, product);
	--print dim edgeIdeal G;

	modifiedIdeal := ideal(parts | edgeIdealGens);
	modifiedIdealDim := time dim(T/modifiedIdeal);
	print modifiedIdealDim;
	return modifiedIdealDim + #parts - numPartsCliques;
);
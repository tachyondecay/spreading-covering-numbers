-- Macaulay2 function for computing the covering number of S_n(d)
--
-- This algorithm uses the same logic as its spreading number counterpart: 
-- find an upper bound, then iterate over all possible covers in the degre 
-- below this bound to see if a smaller cover exists. Minimize this cover and 
-- repeat.
--
-- v1.0
-- Ben Babcock <bababcoc@lakeheadu.ca>
------------------------------------------------------------------------------

needsPackage "EdgeIdeals";

-- Iterate over all the covers of a degree until a smaller cover is found
--
-- Required Parameters
--	S		The ring QQ[x_1..x_n]
--	G		The graph S_n(d)
--	upwardCliques	All the upward cliques in G
--	W		The working upward clique cover
--	Legend		A hash table encoding vertices z_i => monomials in S
--	inverseLegend	A hash table encoding monomials in S => vertices z_i
--
checkCover = (S, G, upwardCliques, W, Legend, inverseLegend) -> (
    T := ring G;
	-- Recover n,d
	n := numgens S;
	d := first degree first keys inverseLegend;

    -- Get the symmetric group of degree n
    sGroup := symmetricGroup S;

    while true do (
	print W;
	-- W is our working cover. We need to check for smaller covers.
	targetSize := #W - 1;
	print("Target size is: " | targetSize);

	-- Check if the target size is smaller than a known lower bound
	if targetSize < #(vertices G)//n then break;

	-- Generate all the rotations and reflections of our working cover
	coverImages := for i when i < #sGroup list (
	    sigma := sGroup#i;
	    
	    for j when j < #W list (
		apply(W#j, k -> value apply(factor k, f -> (x_(sigma#(index(f#0)) + 1)^(f#1))))
	    )
	);

	-- Now we iterate through the clique combinations. Since we know the n cliques identified 
	-- by x_i^(d-1) must belong to any cover, we only need to generate combinations of sets of 
	-- size targetSize - n.
	combo := toList(1..(targetSize - n));
	cliquePool := new MutableHashTable from upwardCliques;
	guaranteedCliques := for i from 1 to n list upwardCliques#(x_i^(d - 1)) do remove(cliquePool, x_i^(d - 1));
	numChecked := 0;
	print "Checking combinations.";
	time passed := while true do (
		-- Check if the last combination was empty (i.e., no more covers)
		if #combo == 0 then break {};

		-- Create the corresponding "cover" from the combination
		potentialCover := guaranteedCliques | apply(combo, i -> (values cliquePool)#(i - 1));
		numChecked = numChecked + 1;
	    
		if #(unique flatten potentialCover) == #(vertices G) then break potentialCover;

		combo = nextCombination(#cliquePool, combo);
	);

	print("Checked " | numChecked | " sets.");
    
	if #passed == 0 then break
	else (
		print("Found potential cover " | toString(passed));
	    W = getMinimalCover(G, upwardCliques, passed, Legend, inverseLegend);
	);
    );
    return W;
);

-- This is the main event.
-- Required Parameters
--	n 	The number of indeterminates, x_1..x_n
--	d	The degree of the monomials that interest us
-- Options
--	OutputSet	Boolean. When true, output the minimum upward clique 
--			cover. When false, output just the number.  Default false.
symCoveringNumber = method(Options => {OutputSet => false});
symCoveringNumber(ZZ,ZZ) := opts -> (n,d) -> (
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

    -- Find all upward cliques (each is identified by a monomial from S_n(d - 1))
    SdMinus1 := flatten entries gens((monomialIdeal(gens S))^(d - 1));
    upwardCliques := hashTable apply(SdMinus1, i -> ({i, for j from 1 to n list i*x_j}));

    -- Our initial set, for the cover generator, will be the cliques containing 
    -- x_1^d,...,x_n^d, because these each belong to one and only one clique.
    upCover := getMinimalCover(G, upwardCliques, for i from 1 to n list upwardCliques#(x_i^(d - 1)), legend, inverseLegend);
    
    finalSet := checkCover(S, G, upwardCliques, upCover, legend, inverseLegend);

    if opts.OutputSet then return finalSet
    else return #finalSet;
);


-- Generates a minimal cover of G using only upward cliques
getMinimalCover = (G, upwardCliques, upCover, Legend, inverseLegend) -> (
    -- Get a list of all vertices in the cover
    W := flatten upCover;
    coveredVertices := unique apply(W, w -> inverseLegend#w);

    while true do (
	uncoveredVertices := toList(set(vertices G) - coveredVertices);
	if #uncoveredVertices == 0 then break;

	-- Select a random vertex and find the upward cliques associated with it
	v := Legend#(uncoveredVertices#(random(0, #uncoveredVertices - 1)));
	U := select(values upwardCliques, i -> member(v, i));

	candidateClique := first U;
	for i from 1 when i < #U do (
	    -- Determine how many vertices are in the cover
	    vInCover := select(U#i, j -> member(j, W));
	    if #vInCover == 0 or #vInCover < #select(candidateClique, j -> member(j, W)) then candidateClique = U#i;
	);

	-- Add the candidate clique to the cover
	upCover = append(upCover, candidateClique);
	coveredVertices = coveredVertices | apply(candidateClique, w -> inverseLegend#w);
    );

    -- Minimize the cover
    while true do (
	-- Get the frequency for each vertex (how many cliques contain it)
	vertexFreq := new MutableHashTable;
	for i when i < #upCover do (
	    for j when j < #(upCover#i) do (
		v := (upCover#i)#j;
		if vertexFreq#?v then vertexFreq#v = vertexFreq#v + 1
		else vertexFreq#v = 1;
	    );
	);

	-- Iterate over the cliques. If there is a clique in which no vertex is of frequency
	-- 1, then the clique is not essential to the cover and may be discarded
	discard := for i when i < #upCover do (
			c := upCover#i;
			essential := false;
			for j when j < #c do (
			    if vertexFreq#(c#j) == 1 then (essential = true; break;);
			);
			if not essential then break i;
		    );

	if discard =!= null then upCover = drop(upCover, {discard,discard})
	else break;
    );

    return upCover;
);


-- Generate the next r-combination from a list m of r elements (lexicographical order)
-- m is a subset of {1,..n}
nextCombination = (n,m) -> (
    r := #m;
    if r > n then return {};

    -- Check if the subset is equal to {n - r + 1,...,n}
    if m == toList((n - r + 1)..n) then return {};

    m = new MutableList from m;
    i := r;

    while m#(i - 1) == (n - r + i) do i = i - 1;
    m#(i - 1) = m#(i - 1) + 1;

    for j from (i + 1) to r do m#(j - 1) = m#(i - 1) + j - i;

    return (new List from m);
);


-- Return a list of elements of the symmetric group of degree n
symmetricGroup = method();
symmetricGroup(Ring) := R -> (
    -- This line from the Monomial Ideals chapter, by Serkan Hosten and Gregory Smith, 
    -- of Computations in Algebraic Geometry with Macaulay2
    L := terms det matrix table(numgens R, gens R, (i,r) -> r^(i + 1));
    sGroup := {};

    -- Construct a hashtable to represent each permutation (starting from 0 instead of 1)
    for i from 0 to (#L - 1) do (
	elem := {};
	f := factor L#i;
	for j from 0 to (#f - 1) do (
	    if index f#j#0 =!= null then elem = append(elem, {index f#j#0, f#j#1 - 1});
	);
	sGroup = append(sGroup, hashTable elem);
    );

    return sGroup;
);

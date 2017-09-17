-- section linear_algebra

-- parameter ( k : Type )
-- parameter [ field k ]

-- class vector_space ( V : Type ) extends add_group V := 
--   ( scalar_multiplication : k → V → V )

--   ( module : ∀ ( c d : k ) ( v : V ), scalar_multiplication c (scalar_multiplication d v) = scalar_multiplication (c * d) v )
--   ( unital_module : ∀ ( c d : k ) ( v : V ), scalar_multiplication c (scalar_multiplication d v) = scalar_multiplication (c * d) v )
--   ( distributivity : ∀ ( c : k ) ( u v : V ), scalar_multiplication c (u + v) = ( scalar_multiplication c u) + (scalar_multiplication c v) )
--   -- axioms

-- parameter ( U : Type )
-- parameter [ vector_space U ]
-- parameter ( V : Type )
-- parameter [ vector_space V ]
-- parameter ( W : Type )
-- parameter [ vector_space W ]

-- structure linear_map ( U V : Type ) [ vector_space U ] [ vector_space V ] := 
--   ( map : U → V )
--   -- linearity

-- instance linear_maps : vector_space (linear_map U V) := sorry

-- structure bilinear_map ( U V W : Type ) [ vector_space U ] [ vector_space V ] [ vector_space W ] := 
--   ( map : U → V → W )
--   -- left and right linearity

-- class associative_algebra ( V : Type ) [ vector_space V ] :=
--   ( multiplication : bilinear_map V V V )
--   ( unit           : V )
  
--   ( associativity  : ∀ u v w : V, multiplication.map (multiplication.map u v) w = multiplication.map u (multiplication.map v w) )
--   -- other axioms

-- instance End ( V : Type ) [ vector_space V ] : associative_algebra (linear_map V V) := sorry

-- end linear_algebra
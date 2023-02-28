import tactic topology.basic
open classical topological_space


-- El conjunt buit és un conjunt obert en qualsevol topologia.
theorem BuitObert {X: Type} (h1: topological_space X) : (h1.is_open (∅ : set X)) :=
begin
	let Z := (∅ : set (set X)),
	have h2 : ∀ z ∈ Z, h1.is_open z,
	intro z,
	assume h3,
	exact false.elim h3,
	sorry,
end

-- La topologia discreta és una topologia.
instance TopDisc {X: Type} : topological_space X := 
begin
	-- Definim la topologia discreta
	let TD : set X → Prop := λ(U: set X), true,

	use TD,
	-- Objectiu 1: Intersecció
	{ intros A B,
	  assume h1 h2,
	  exact true.intro, },
	-- Objectiu 2: Unió arbitrària
	{ intro I,
	  intro A,
	  exact true.intro, },
end

-- La topologia trivial és una topologia.
instance TopTriv {X: Type} : topological_space X :=
begin
	-- Definim la topologia trivial
	let TT: set X → Prop :=
	begin
		intro U,
		exact (U = set.univ) ∨ (U = (∅ : set X)),
  end,

	use TT,
	-- Objectiu 1: Total
	{ have h1: set.univ = set.univ,
		 refl,
	 exact or.inl h1, },

	-- Objectiu 2: Intersecció
	{ intros A B,
		assume h1 h2,
		cases h1 with hAU hAE,
		-- Cas 2.1: A = set.univ
		{ have h3 : A ∩ B = B,
				ext z,
				split,
				-- Subojectiu 2.1.1
				{ assume h4,
					exact and.elim_right h4, },
				-- Subojectiu 2.1.2
				{ assume h4,
					have h5 : z ∈ A,
						exact filter.mem_top.mpr hAU z,
					exact and.intro h5 h4, },
					rw h3,
					exact h2, },
		-- Cas 2.2: A = ∅
		{ have h3: A∩B = (∅: set X),
				ext z,
				split,
				-- Subojectiu 2.2.1
				{ rw hAE,
					assume h3,
					exact and.elim_left h3, },
				-- Subojectiu 2.2.2
				{ rw hAE,
					assume h3,
					exact false.rec (z ∈ ∅ ∩ B) h3, },
			rw h3,
			have h4: ∅ = ∅,
				refl,
			exact or.inr h4, }, },

	-- Objectiu 3: Unió arbitrària
	-- TODO: Corregir l'estil del codi
	{ intro 𝔸,
		intro h1,
		have h2: ∀ (t : set X), t ∈ 𝔸 → t = set.univ ∨ t = (∅: set X),
			exact h1,
		have h3: (∀ (t: set X), t ∈ 𝔸 → t = (∅: set X)) ∨ ¬(∀ (t: set X), t ∈ 𝔸 → t = (∅: set X)),
			exact classical.em (∀ (t : set X), t ∈ 𝔸 → t = ∅),
		cases h3 with h3A h3B,
		have h4: ⋃₀ 𝔸 = (∅ : set X),
		ext z,
		split,
		assume h4,
		cases h4 with T hT,
		cases hT with hT hz,
		have h5: T = (∅: set X),
		apply h3A,
		exact hT,
		rw h5 at hz,
		exact hz,
		assume h4,
		exact false.rec (z ∈ ⋃₀ 𝔸) h4,
		rw h4,
		have h5: ∅ = ∅,
			refl,
		exact or.inr h5,
		have h5 : ∃ (t : set X), ¬(t ∈ 𝔸 → t = (∅ : set X)),
		exact not_forall.mp h3B,
		cases h5 with T hT,
		simp at hT,
		cases hT with hT hT1,
		have h6 : TT T,
		exact h1 T hT,
		have h7 : T = set.univ,
		cases h6,
		assumption, --exact h6,
		by_contra,
		exact hT1 h6,
		have h8 : ⋃₀ 𝔸 = set.univ,
		ext z,
		split,
		assume h8,
		exact set.mem_univ z,
		assume h8,
		rw h7.symm at h8,
		use T,
		exact and.intro hT h8,
		exact or.inl h8, },
end

-- La topologia cofinita és una topologia.
instance TopCof (X: Type) : topological_space X :=
begin
	-- Definim la topologia cofinita
	let TC : set X → Prop := λ(A: set X), (A = (∅ : set X)) ∨ (set.finite (Aᶜ)),

	use TC,
	sorry,
	sorry, 
	sorry,
end

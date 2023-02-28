import tactic topology.basic data.set.basic data.real.basic
import topologies
open classical topological_space

-- Reals positius
def preal := {y: ℝ | 0 < y}

-- Invers d'un natural positiu
noncomputable def InversN (n : pnat) : preal :=
begin
	use n⁻¹,
	sorry,
end


-- Definició d'espai métric.
structure EspaiMetric (X : Type) :=
(d : X × X → ℝ)
(no_deg : ∀ (x y : X), d(x, y) = 0 ↔ x = y)
(sim : ∀ (x y : X), d(x, y) = d(y, x))
(triang : ∀ (x y z : X), d(x, z) ≤ d(x, y) + d(y, z))

-- La distància d'un espai métric és definida positiva.
theorem def_pos (X: Type) (em : EspaiMetric X) : ∀(x y : X), em.d(x, y) ≥ 0 :=
begin
	intros x y,
	have h1 : em.d(x, x) ≤ em.d(x,y) + em.d(y, x),
		exact em.triang x y x,
	have h2 : x = x,
		refl,
	have h3 : em.d(x,x) = 0,
		exact (em.no_deg x x).mpr rfl,
	rw h3 at h1,
	rw em.sim x y at h1,
	have h4 : em.d(y, x) + em.d(y, x) = 2 * em.d(y, x),
		linarith,
	rw h4 at h1,
	rw em.sim at h1,
	linarith,
end

-- Definició de bola oberta.
def Bola (X: Type) (em : EspaiMetric X) (x: X) (ε: preal) : set X :=
{y : X | em.d(x, y) < ε}

--section MetricaDiscreta 
--noncomputable def dD (X: Type)  : X × X → ℝ :=
--begin
--rintro ⟨x, y⟩,
----have h1 : (x = y) ∨ (¬ (x = y)),
----exact classical.em (x = y), 
--by_cases h1 : x = y,
--exact 0,
--exact 1,
--end
--
--noncomputable theorem TD (X: Type) : EspaiMetric X :=
--begin
--use dD X,
---- Ax2.
--intros x y,
--split,
----
--assume h1,
--rw dD at h1,
--simp at h1,
--exact not_ne_iff.mp h1,
----
--assume h1,
--rw h1,
--have h2 : y = y,
--refl,
--sorry,
--end
--
--end MetricaDiscreta

section ValorAbsolut
def dVAbs : ℝ × ℝ → ℝ :=
begin
	rintros ⟨x, y⟩,
	exact abs(x-y),
end

noncomputable theorem EspaiMetricVAbs : EspaiMetric ℝ :=
begin
	use dVAbs,
	-- Objectiu 1: No degeneració
	{ intros x y,
		split,
		{ assume h1,
			rw dVAbs at h1,
			simp at h1,
			linarith, },
		{ assume h1,
			rw dVAbs,
			simp,
			linarith, }, },
	-- Objectiu 2: Simetria
	{ rw dVAbs,
		simp,
		intros x y,
		exact abs_sub_comm x y, },

	-- Objectiu 3: Desigualtat triangular
	{ intros x y z,
		rw dVAbs,
		simp,
		exact abs_sub_le x y z, },
end
end ValorAbsolut

section TopologiaMetrica
-- Definició de topologia associada a un espai métric.
def TopologiaMetrica (X: Type) (em: EspaiMetric X) : set X → Prop :=
begin
	assume A,
	exact (∀ (x : A), ∃ (ε : preal), Bola X em x ε ⊆ A), 
end

-- La topologia associada a un espai métric és una topologia.
noncomputable theorem EspaiMetricTop (X: Type) (em: EspaiMetric X) : topological_space X :=
begin
	use TopologiaMetrica X em,
	{sorry, },
	{sorry, },
	{sorry, },
end
end TopologiaMetrica

-- -- Donades dues topologies sobre un mateix conjunt, direm que ...
-- def Menorque {X : Type} : (set X → Prop) → (set X → Prop) → Prop :=
-- λ (T S : set X → Prop), ∀ (A: set X), T A → S A

-- def ExtraccioTop {X: Type} (h1: topological_space X) : set X → Prop :=
-- begin
-- exact h1.is_open,
-- end

-- theorem DiscContainer (X: Type) (h1: topological_space X) :
-- 	Menorque (ExtraccioTop h1) (ExtraccioTop TopDisc) :=
-- begin
-- 	rw Menorque,
-- 	intro A,
-- 	assume h2,
-- 	exact true.intro, -- exact trivial,
-- end

-- Definició de conjunt tancat.
def es_tancat {X: Type} (top : topological_space X) : set X → Prop :=
begin
	intro C,
	exact top.is_open (Cᶜ),
end

-- El conjunt total és tancat.
theorem TotalTancat {X : Type} (top : topological_space X) : (es_tancat top set.univ) :=
begin
	rw es_tancat,
	have h2: set.univᶜ = (∅: set X),
		exact set.compl_univ,
	rw h2,
	exact BuitObert top,
end

-- El conjunt buit és tancat.
theorem BuitTancat {X : Type} (top : topological_space X) : (es_tancat top (∅ : set X)) :=
begin
	rw es_tancat,
	have h2: (∅ : set X)ᶜ = set.univ,
		exact set.compl_empty,
	rw h2,
	exact top.is_open_univ,
end

-- Definició d'entorn d'un punt.
def es_entorn {X : Type} (top : topological_space X) : set X → X → Prop :=
begin
	intro U,
	intro x,
	exact (∃ (A : set X), (top.is_open A) ∧ (x ∈ A) ∧ (A ⊆ U)),
end

def Entorns {X : Type} (top : topological_space X) (x : X) : set (set X) :=
	{U: set X | es_entorn top U x}

def EntornSubconjunt {X: Type} (top : topological_space X) (x : X) (A : set X) : set (set X):=
	{U ∈ Entorns top x | U ⊆ A}

def ObertEnmig {X: Type} (top : topological_space X) (x : X) (A : set X) : set (set X) :=
	{U : set X | top.is_open U ∧ x ∈ U ∧ U ⊆ A}

def MaxObertEnmig {X: Type} (h1: topological_space X) (x: X) (A: set X) : set X :=
	⋃₀ (ObertEnmig h1 x A)

theorem MOEObert {X: Type} (top : topological_space X) (x: X) (A: set X) :
top.is_open (MaxObertEnmig top x A) :=
begin
	have h2 : (∀ (t : set X), t ∈ (ObertEnmig top x A) → top.is_open t),
		intros t ht,
		rw ObertEnmig at ht,
		cases ht with ht1 ht2,
		exact ht1,
	exact top.is_open_sUnion (ObertEnmig top x A) h2,
end

def Proba {X: Type} (top : topological_space X) (A: set X) : set (set X) := 
	{U : set X | ∃ (x: X), U = MaxObertEnmig top x A}

def ProbaTot {X : Type} (top : topological_space X) (A: set X) : set X :=
	⋃₀ (Proba top A)

theorem PTObert {X : Type} (top : topological_space X) (A: set X) : top.is_open (ProbaTot top A) :=
begin
	rw ProbaTot,
	rw Proba,
	have h2: ∀ (t : set X), t ∈ {U : set X | ∃ (x : X), U = MaxObertEnmig top x A} → top.is_open t,
	intros t ht,
	cases ht with x hx,
	rw hx,
	exact MOEObert top x A,
	exact top.is_open_sUnion (Proba top A) (h2),
end

theorem EntornIgual {X: Type} (top : topological_space X) (A: set X) (h2 : ∀ (x : X), x ∈ A → A ∈ Entorns top x): 
ProbaTot top A = A :=
begin
	ext z,
	split,
	assume h3,
	cases h3 with A1 h3,
	cases h3 with hA1 hz,
	cases hA1 with x hx,
	rw MaxObertEnmig at hx,
	rw ObertEnmig at hx,
	--have h3 : ⋃₀ {U : set X | h1.is_open U ∧ x ∈ U ∧ U ⊆ A} = A1,
	--exact hx.symm,
	--have h3 : A1 ⊆ A,
	rw hx at hz,
	cases hz with A2 hA2,
	cases hA2 with hA2 h3,
	--cases hA2 with hA2a hA2b,
	--cases hA2b with hA2b hA2c,
	exact (hA2.elim_right).elim_right h3,
	assume h3,
	specialize h2 z h3,
	cases h2 with U hU,
	use (MaxObertEnmig top z A),
	split,
	use z,
	use U,
	exact and.intro hU (hU.elim_right).elim_left,
end

theorem ObertEntornSii (X: Type) (top : topological_space X) (A: set X) : 
top.is_open A ↔ (∀ (x ∈ A), A ∈ (Entorns top x)) :=
begin
	split,
	---
	intro h2,
	intros x hx,
	rw Entorns,
	rw es_entorn,
	simp,
	use A,
	split,
	exact h2,
	split,
	exact hx,
	exact rfl.subset,

	---
	intro h2,
	have h3: ∀ (x ∈ A), ∃ (A_1 : set X), top.is_open A_1 ∧ x ∈ A_1 ∧ A_1 ⊆ A,
	intro x,
	specialize h2 x,
	exact h2,
	rw (EntornIgual top A h2).symm,
	rw ProbaTot,
	have h4: ∀ (t ∈ Proba top A), top.is_open t,
	intros t hT,
	cases hT with z hz,
	specialize h3 z,
	rw hz,
	exact MOEObert top z A,
	exact top.is_open_sUnion (Proba top A) h4,
end

-- Definició de base d'entorns.
structure BaseEntorns (X : Type) (top : topological_space X) (x : X) :=
	(B : set (set X))
	(Ax1 : ∀ (U ∈ B), U ∈ (Entorns top x))
	(Ax2 : ∀ (V ∈ (Entorns top x)), ∃ (U ∈ B), U ⊆ V)

noncomputable theorem BaseTopMetrica (X : Type) (em : EspaiMetric X) (x : X) : BaseEntorns X (EspaiMetricTop X em) x :=
begin
	let B := {U : set X | ∃ (n : pnat), U = Bola X em x (InversN n)},
	use B,
	{ intros U hU,
		cases hU with n hn,
		rw hn,
		rw Entorns,
		rw es_entorn,
		simp,
		use (Bola X em x (InversN n)),
		split, 
		sorry, sorry, },
	{ sorry, },
end

structure BaseOberts (X : Type) (top : topological_space X) :=
  (B : set (set X))
	(Ax1 : ∀ (U ∈ B), top.is_open U)
	(Ax2 : ∀ (A : set X), top.is_open A → ∃ (𝕌 ⊆ B), A = ⋃₀ 𝕌)

structure BaseOberts2 (X : Type) (top : topological_space X) :=
	(B : set (set X))
	(Ax1 : ∀ (U ∈ B), top.is_open U)
	(Ax2 : ∀ (A : set X), ∀ (x : X), top.is_open A ∧ x ∈ A → ∃ (U ∈ B), x ∈ U ∧ U ⊆ A)

theorem BaseOberts12 (X : Type) (top : topological_space X) (BO : BaseOberts X top) : (∀ (A : set X), ∀ (x : X), top.is_open A ∧ x ∈ A → ∃ (U ∈ BO.B), x ∈ U ∧ U ⊆ A) :=
begin
	sorry,
end

theorem BaseOberts21 (X : Type) (top : topological_space X) (BO : BaseOberts2 X top) : (∀ (A : set X), top.is_open A → ∃ (𝕌 ⊆ BO.B), A = ⋃₀ 𝕌) :=
begin
	sorry,
end

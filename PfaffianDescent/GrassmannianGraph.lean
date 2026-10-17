import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace PfaffianDescent
open Module
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- The quotient by a graph is the second factor, by subtracting the graph value. -/
noncomputable def graphQuotientEquiv (f : M →ₗ[R] N) : ((M × N) ⧸ f.graph) ≃ₗ[R] N :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.graph_eq_ker_coprod f)).trans
    (((-f).coprod LinearMap.id).quotKerEquivOfSurjective (by
      intro y
      exact ⟨(0, y), by simp⟩))

lemma graphQuotientEquiv_mk (f : M →ₗ[R] N) (x : M × N) :
    graphQuotientEquiv f (Submodule.Quotient.mk x) = x.2 - f x.1 := by
  change -f x.1 + x.2 = x.2 - f x.1
  abel

/-- The second-factor coordinate map into a submodule's quotient. It defines
one of the Grassmannian's standard open-chart conditions. -/
def graphChartQuotientMap (W : Submodule R (M × N)) : N →ₗ[R] ((M × N) ⧸ W) :=
  W.mkQ.comp (LinearMap.inr R M N)

lemma graphChartQuotientMap_graph_bijective (f : M →ₗ[R] N) :
    Function.Bijective (graphChartQuotientMap f.graph) := by
  have he (y : N) : graphQuotientEquiv f (graphChartQuotientMap f.graph y) = y := by
    change graphQuotientEquiv f (Submodule.Quotient.mk (0, y)) = y
    simp [graphQuotientEquiv_mk]
  constructor
  · intro y z h
    have hh := congrArg (graphQuotientEquiv f) h
    simpa only [he] using hh
  · intro x
    refine ⟨graphQuotientEquiv f x, (graphQuotientEquiv f).injective ?_⟩
    exact he _

/-- Every quotient satisfying the standard chart condition is a unique graph.
This works over arbitrary commutative rings, including rings with nilpotents. -/
theorem graphChartQuotientMap_bijective_iff (W : Submodule R (M × N)) :
    Function.Bijective (graphChartQuotientMap W) ↔ ∃! f : M →ₗ[R] N, W = f.graph := by
  constructor
  · intro h
    let e := LinearEquiv.ofBijective (graphChartQuotientMap W) h
    let f : M →ₗ[R] N := -(e.symm.toLinearMap.comp (W.mkQ.comp (LinearMap.inl R M N)))
    have he (x : M × N) : e.symm (W.mkQ x) = -f x.1 + x.2 := by
      have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
      conv_lhs => rw [hx]
      rw [map_add, map_add]
      have hy : e.symm (W.mkQ (0, x.2)) = x.2 := e.symm_apply_apply x.2
      rw [hy]
      simp [f]
    have hW : W = f.graph := by
      ext x
      rw [LinearMap.mem_graph_iff, ← Submodule.Quotient.mk_eq_zero]
      change W.mkQ x = 0 ↔ _
      rw [← (map_eq_zero_iff e.symm e.symm.injective), he]
      rw [add_comm, ← sub_eq_add_neg, sub_eq_zero]
    refine ⟨f, hW, ?_⟩
    intro g hg
    apply LinearMap.ext
    intro a
    have ha : (a, g a) ∈ f.graph := hW ▸ hg.symm ▸ (show (a, g a) ∈ g.graph from rfl)
    exact ha
  · rintro ⟨f, rfl, _⟩
    exact graphChartQuotientMap_graph_bijective f

end
section
variable {R : Type*} [CommRing R] {m n : ℕ}

/-- A graph gives an actual point of Mathlib's quotient Grassmannian. -/
noncomputable def graphGrassmannian (f : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n where
  toSubmodule := f.graph
  finite_quotient := Module.Finite.equiv (graphQuotientEquiv f).symm
  projective_quotient := Module.Projective.of_equiv (graphQuotientEquiv f).symm
  rankAtStalk_eq p := by
    have : Nontrivial R := (algebraMap R (Localization.AtPrime p.asIdeal)).domain_nontrivial
    rw [Module.rankAtStalk_eq_of_equiv (graphQuotientEquiv f), Module.rankAtStalk_eq_finrank_of_free]
    simp

/-- The standard Grassmannian chart determined by the second coordinate block. -/
def GrassmannianGraphChart (R : Type*) [CommRing R] (m n : ℕ) :=
  {W : Module.Grassmannian R ((Fin m → R) × (Fin n → R)) n //
    Function.Bijective (graphChartQuotientMap W.toSubmodule)}

/-- Standard Grassmannian-chart points are arbitrary matrices, without extra
rank, splitting, or reducedness assumptions on the coefficient ring. -/
noncomputable def grassmannianGraphChartEquiv :
    ((Fin m → R) →ₗ[R] (Fin n → R)) ≃ GrassmannianGraphChart R m n :=
  Equiv.ofBijective (fun f => ⟨graphGrassmannian f, graphChartQuotientMap_graph_bijective f⟩) (by
    constructor
    · intro f g h
      have he : f.graph = g.graph := congrArg (fun W => W.1.toSubmodule) h
      apply LinearMap.ext
      intro a
      exact (show (a, f a) ∈ g.graph from he ▸ (show (a, f a) ∈ f.graph from rfl))
    · rintro ⟨W, hW⟩
      obtain ⟨f, hf, _⟩ := (graphChartQuotientMap_bijective_iff W.toSubmodule).mp hW
      refine ⟨f, Subtype.ext ?_⟩
      exact Module.Grassmannian.ext hf.symm)

/-- A standard chart of `Gr(3,6)` has nine independent affine parameters. -/
noncomputable def grassmannianMatrixChartEquiv :
    Matrix (Fin n) (Fin m) R ≃ GrassmannianGraphChart R m n :=
  Matrix.toLin'.toEquiv.trans grassmannianGraphChartEquiv

end
end PfaffianDescent

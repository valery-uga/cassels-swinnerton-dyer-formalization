import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Order
universe u

attribute [local instance] specializationOrder

lemma topologicalKrullDim_eq_pointKrullDim (X : Type*) [TopologicalSpace X]
    [QuasiSober X] [T0Space X] : topologicalKrullDim X = krullDim X :=
  krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- An upper bound on all open charts is an upper bound on the whole scheme. -/
lemma scheme_dimension_le_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    (d : WithBot ℕ∞) (h : ∀ i, topologicalKrullDim (𝒰.X i) ≤ d) :
    topologicalKrullDim X ≤ d := by
  rw [topologicalKrullDim_eq_pointKrullDim, krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  have he : coheight x = coheight y := by
    exact (congrArg (fun z : X => coheight z) hy).symm.trans
      (Topology.IsOpenEmbedding.coheight_eq _ (𝒰.f (𝒰.idx x)).isOpenEmbedding)
  calc
    (coheight x : WithBot ℕ∞) = coheight y := congrArg _ he
    _ ≤ krullDim (𝒰.X (𝒰.idx x)) := coheight_le_krullDim y
    _ = topologicalKrullDim (𝒰.X (𝒰.idx x)) :=
      (topologicalKrullDim_eq_pointKrullDim _).symm
    _ ≤ d := h _

/-- A nonempty atlas of charts of one dimension determines the scheme's dimension. -/
lemma scheme_dimension_eq_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    (i : 𝒰.I₀) (d : WithBot ℕ∞) (h : ∀ j, topologicalKrullDim (𝒰.X j) = d) :
    topologicalKrullDim X = d := by
  apply le_antisymm (scheme_dimension_le_of_openCover 𝒰 d fun j => (h j).le)
  rw [← h i]
  exact (𝒰.f i).isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- The underlying space of affine `n`-space over a field has dimension `n`. -/
lemma polynomialSpec_dimension (K : Type u) [Field K] (ι : Type) [Finite ι] :
    topologicalKrullDim (Spec (.of (MvPolynomial ι K))) = (Nat.card ι : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial ι K)) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

end PfaffianDescent

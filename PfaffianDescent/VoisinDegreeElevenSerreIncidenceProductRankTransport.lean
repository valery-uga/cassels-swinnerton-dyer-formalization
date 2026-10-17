import PfaffianDescent.VoisinDegreeElevenSerreIncidenceParameterRankChartMap
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeRowIdealGluing

/-! # Actual configuration-product and equation transport under the global section rank equality -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def serreIncidenceProductRankIso
    {K : Type u} [CommRing K] {B : Scheme.{u}} (b : B ⟶ Spec (.of K))
    {n m : ℕ} (h : n = m) :
    pullback b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) ≅
    pullback b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) :=
  eqToIso (congrArg (fun q => pullback b
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin q) K)))) h)

def serreIncidenceRankProductChart
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n) :
    pullback b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j))) ⟶
    pullback b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ chartι _ j) (by
    rw [Category.assoc, chartι_toBase]
    exact pullback.condition)

def serreIncidenceRankProductRow
    {K : Type u} [CommRing K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) {n : ℕ} (j : Fin n)
    (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤)) (r : Fin 6) :
    Γ(pullback b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j))), ⊤) :=
  ∑ k : Fin n,
    (pullback.snd b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j)))).appTop
      ((Scheme.ΓSpecIso (.of (ChartRing (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin n) K)) j))).inv
          (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j k)) *
    (pullback.fst b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) j)))).appTop (A r k)

theorem serreIncidenceProductRankIso_inv_fst
    {K : Type u} [CommRing K] {B : Scheme.{u}} (b : B ⟶ Spec (.of K))
    {n m : ℕ} (h : n = m) :
    (serreIncidenceProductRankIso b h).inv ≫ pullback.fst b
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))) =
    pullback.fst b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) := by
  subst m
  simp [serreIncidenceProductRankIso]

theorem serreIncidenceProductRank_equations
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) {n : ℕ} (h9 : n = 9)
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin n) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin n) Γ(B, ⊤))
    (h : ∀ j : Fin n, I.comap (serreIncidenceRankProductChart b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceRankProductRow b j A)))) :
    ∀ j : Fin 9,
      (I.comap (serreIncidenceProductRankIso b h9).inv).comap
        (serreIncidenceNativeAmbientChartToProduct b j) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span (Set.range
        (serreIncidenceNativeProductEvaluationRow b j
          (fun r k => A r ((finCongr h9).symm k))))) := by
  subst n
  intro j
  simp only [serreIncidenceProductRankIso, eqToIso_refl, Iso.refl_inv,
    Scheme.IdealSheafData.comap_id, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  change I.comap (serreIncidenceRankProductChart b j) =
    Scheme.IdealSheafData.ofIdealTop
      (Ideal.span (Set.range (serreIncidenceRankProductRow b j A)))
  exact h j

end PfaffianDescent

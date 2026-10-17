import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeChartRows
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelIncidenceGluing
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceSpecKernelIdeal
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualAffineIdealComap

/-! # Literal native evaluation equations identify the actual global incidence ideal -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

lemma serreIncidenceSpan_map_range
    {R S : Type u} [CommRing R] [CommRing S] {ι : Type*}
    (φ : R →+* S) (f : ι → R) (g : ι → S) (h : ∀ i, φ (f i) = g i) :
    (Ideal.span (Set.range f)).map φ = Ideal.span (Set.range g) := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact h i

def serreIncidenceNativeProductEvaluationRow
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤)) (r : Fin 6) :
    Γ(pullback b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j))), ⊤) :=
  ∑ k : Fin 9,
    (pullback.snd b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j)))).appTop
      ((Scheme.ΓSpecIso (.of (ChartRing (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) K)) j))).inv
          (chartCoordinate (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j k)) *
    (pullback.fst b (Spec.map (CommRingCat.ofHom (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K)) j)))).appTop (A r k)

theorem serreIncidenceIdeal_eq_kernelProj_of_native_rows
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K))
    (I : (pullback b (toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 9) K)))).IdealSheafData)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤))
    (h : ∀ j : Fin 9,
      I.comap (serreIncidenceNativeAmbientChartToProduct b j) =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range (serreIncidenceNativeProductEvaluationRow b j A)))) :
    I.comap (serreIncidenceNativeAmbientProjectiveIso b).hom =
      (schemeQuotientMap (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (serreEvaluationHomogeneousIdeal A) bot_le).ker := by
  apply serreIncidenceIdeal_eq_kernelProj_of_chart_equations b I A
  intro j
  let e := serreIncidenceNativeAmbientChartIso b j
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)) := ⊥
  let f : Fin 6 → Γ(Spec (.of (ChartRing J j)), ⊤) := fun r =>
    (Scheme.ΓSpecIso (.of (ChartRing J j))).inv
      (∑ k : Fin 9, chartBaseMap J j (A r k) * chartCoordinate J j k)
  have h1 := congrArg (fun P => P.comap e.hom) (h j)
  have h2 := cubicClosedPointSerreFiniteZeroResidual_affineIdeal_comap e.hom
    (Ideal.span (Set.range (serreIncidenceNativeProductEvaluationRow b j A)))
  have h3 := serreIncidenceSpan_map_range e.hom.appTop.hom
    (serreIncidenceNativeProductEvaluationRow b j A) f
    (fun r => serreIncidenceNativeAmbientChart_evaluation_row b j A r)
  exact h1.trans (h2.trans ((congrArg Scheme.IdealSheafData.ofIdealTop h3).trans
    (serreEvaluationKernel_projective_chart_equations A j).symm))

end PfaffianDescent

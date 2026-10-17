import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeChartParameterFunctions

/-! # Native marked evaluation rows are exactly the homogeneous kernel chart rows -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

lemma serreIncidenceEvaluationRow_transport
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {ι : Type*} [Fintype ι] (f : S →+* T) (g : R →+* T)
    (c a : ι → S) (c' a' : ι → R)
    (hc : ∀ k, f (c k) = g (c' k)) (ha : ∀ k, f (a k) = g (a' k)) :
    f (∑ k, c k * a k) = g (∑ k, a' k * c' k) := by
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, map_mul, hc k, ha k, mul_comm]

theorem serreIncidenceNativeAmbientChart_evaluation_row
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) (j : Fin 9)
    (A : Matrix (Fin 6) (Fin 9) Γ(B, ⊤)) (r : Fin 6) :
    let I : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K) := ⊥
    let J : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)) := ⊥
    (serreIncidenceNativeAmbientChartIso b j).hom.appTop
      (∑ k : Fin 9,
        (pullback.snd b (Spec.map (CommRingCat.ofHom (chartBaseMap I j)))).appTop
          ((Scheme.ΓSpecIso (.of (ChartRing I j))).inv (chartCoordinate I j k)) *
        (pullback.fst b (Spec.map (CommRingCat.ofHom (chartBaseMap I j)))).appTop (A r k)) =
    (Scheme.ΓSpecIso (.of (ChartRing J j))).inv
      (∑ k : Fin 9, chartBaseMap J j (A r k) * chartCoordinate J j k) := by
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K) := ⊥
  let J : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤)) := ⊥
  let v := Spec.map (CommRingCat.ofHom (chartBaseMap I j))
  exact serreIncidenceEvaluationRow_transport
    (serreIncidenceNativeAmbientChartIso b j).hom.appTop.hom
    (Scheme.ΓSpecIso (.of (ChartRing J j))).inv.hom
    (fun k => (pullback.snd b v).appTop
      ((Scheme.ΓSpecIso (.of (ChartRing I j))).inv (chartCoordinate I j k)))
    (fun k => (pullback.fst b v).appTop (A r k))
    (chartCoordinate J j) (fun k => chartBaseMap J j (A r k))
    (fun k => serreIncidenceNativeAmbientChart_parameter_function b j k)
    (fun k => serreIncidenceNativeAmbientChart_configuration_function b j (A r k))

end PfaffianDescent

import PfaffianDescent.IncidenceOverlapIsomorphism
import PfaffianDescent.SchemeAffineFunctions

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

/-- Interpret a chart morphism as its actual graph and isotropic forms over global functions. -/
noncomputable def incidenceChartPoint {X : Scheme.{u}} (f : X ⟶ incidenceGraphScheme K) :
    IncidenceGraphPoints Γ(X, ⊤) :=
  (incidenceGraphPointCoordinates Γ(X, ⊤)).symm (fun j => affineFunctionHom f (MvPolynomial.X j))

lemma incidenceChartPoint_coordinates {X : Scheme.{u}} (f : X ⟶ incidenceGraphScheme K) :
    incidenceGraphPointCoordinates Γ(X, ⊤) (incidenceChartPoint K f) =
      fun j => affineFunctionHom f (MvPolynomial.X j) :=
  (incidenceGraphPointCoordinates Γ(X, ⊤)).apply_symm_apply _

lemma incidenceChartPoint_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ incidenceGraphScheme K) :
    incidenceChartPoint K (f ≫ g) = incidenceGraphPointMap f.appTop.hom (incidenceChartPoint K g) := by
  apply (incidenceGraphPointCoordinates Γ(X, ⊤)).injective
  rw [incidenceChartPoint_coordinates, incidenceGraphPointMap_coordinates, incidenceChartPoint_coordinates]
  funext j
  exact RingHom.congr_fun (affineFunctionHom_comp f g) (MvPolynomial.X j)

lemma incidenceChart_morphism_ext {X : Scheme.{u}} (f g : X ⟶ incidenceGraphScheme K)
    (hb : f ≫ incidenceGraphToBase K = g ≫ incidenceGraphToBase K)
    (hp : incidenceChartPoint K f = incidenceChartPoint K g) : f = g := by
  apply affineFunctionHom_injective
  apply MvPolynomial.ringHom_ext'
  · have h := congrArg affineFunctionHom hb
    exact (affineFunctionHom_comp_Spec f MvPolynomial.C).symm.trans
      (h.trans (affineFunctionHom_comp_Spec g MvPolynomial.C))
  · intro j
    have h := congrArg (incidenceGraphPointCoordinates Γ(X, ⊤)) hp
    rw [incidenceChartPoint_coordinates, incidenceChartPoint_coordinates] at h
    exact congrFun h j

lemma incidenceOverlapPolynomial_map {A : Type u} [CommRing A]
    (φ : IncidenceGraphRing K →+* A) (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints A) (hp : incidenceGraphPointCoordinates A p = fun j => φ (MvPolynomial.X j)) :
    φ (incidenceOverlapPolynomial K σ) = graphOverlapDeterminant (graphCoordinatePermutation A σ) p.1 := by
  letI : Algebra K A := (φ.comp MvPolynomial.C).toAlgebra
  have hφ : (MvPolynomial.aeval (R := K) (incidenceGraphPointCoordinates A p)).toRingHom = φ := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change MvPolynomial.aeval (incidenceGraphPointCoordinates A p) (MvPolynomial.C k) = φ (MvPolynomial.C k)
      rw [MvPolynomial.aeval_C]
      rfl
    · intro j
      change MvPolynomial.aeval (incidenceGraphPointCoordinates A p) (MvPolynomial.X j) = φ (MvPolynomial.X j)
      rw [MvPolynomial.aeval_X, hp]
  exact (RingHom.congr_fun hφ (incidenceOverlapPolynomial K σ)).symm.trans
    (incidenceOverlapPolynomial_eval K σ p)

/-- An actual chart morphism factors through the incidence overlap exactly when its graph block is invertible. -/
lemma incidenceChart_factor_iff {X : Scheme.{u}} (f : X ⟶ incidenceGraphScheme K)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    (∃ g : X ⟶ incidenceOverlapScheme K σ, g ≫ incidenceOverlapι K σ = f) ↔
      Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ) (incidenceChartPoint K f).1) := by
  rw [show (∃ g : X ⟶ incidenceOverlapScheme K σ, g ≫ incidenceOverlapι K σ = f) ↔
      IsUnit (affineFunctionHom f (incidenceOverlapPolynomial K σ)) from
        affineLocalization_factor_iff f (incidenceOverlapPolynomial K σ)]
  rw [incidenceOverlapPolynomial_map K (affineFunctionHom f) σ (incidenceChartPoint K f)
    (incidenceChartPoint_coordinates K f), graphOverlapDeterminant_isUnit_iff]

noncomputable def incidenceChartLift {X : Scheme.{u}} (f : X ⟶ incidenceGraphScheme K)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (hf : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ) (incidenceChartPoint K f).1)) :
    X ⟶ incidenceOverlapScheme K σ :=
  affineLocalizationLift f (incidenceOverlapPolynomial K σ)
    ((incidenceOverlapPolynomial_map K (affineFunctionHom f) σ (incidenceChartPoint K f)
      (incidenceChartPoint_coordinates K f)).symm ▸ (graphOverlapDeterminant_isUnit_iff _ _).mpr hf)

lemma incidenceChartLift_fac {X : Scheme.{u}} (f : X ⟶ incidenceGraphScheme K)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (hf : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ) (incidenceChartPoint K f).1)) :
    incidenceChartLift K f σ hf ≫ incidenceOverlapι K σ = f :=
  affineLocalizationLift_fac f _ _

lemma incidenceChartPoint_overlap {X : Scheme.{u}} (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (g : X ⟶ incidenceOverlapScheme K σ) :
    incidenceChartPoint K (g ≫ incidenceOverlapι K σ) =
      incidenceGraphPointMap (affineFunctionHom g) (incidenceOverlapUniversal K σ) := by
  apply (incidenceGraphPointCoordinates Γ(X, ⊤)).injective
  rw [incidenceChartPoint_coordinates, incidenceGraphPointMap_coordinates, incidenceOverlapUniversal_coordinates]
  funext j
  exact RingHom.congr_fun (affineFunctionHom_comp_Spec g (algebraMap _ _)) (MvPolynomial.X j)

lemma incidenceChartPoint_other {X : Scheme.{u}} (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (g : X ⟶ incidenceOverlapScheme K σ) :
    incidenceChartPoint K (g ≫ incidenceOverlapOtherι K σ) =
      incidenceGraphPointMap (affineFunctionHom g) (incidenceOverlapTransitionPoint K σ) := by
  apply (incidenceGraphPointCoordinates Γ(X, ⊤)).injective
  rw [incidenceChartPoint_coordinates, incidenceGraphPointMap_coordinates, incidenceOverlapOtherι_eq]
  funext j
  have h := RingHom.congr_fun (affineFunctionHom_comp_Spec g
    (MvPolynomial.aeval (R := K)
      (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ) (incidenceOverlapTransitionPoint K σ))).toRingHom)
    (MvPolynomial.X j)
  exact h.trans (congrArg (affineFunctionHom g) (MvPolynomial.aeval_X _ j))

/-- The actual scheme transition acts on global functions by the full incidence-point transition. -/
lemma incidenceChartPoint_transition {X : Scheme.{u}} (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (g : X ⟶ incidenceOverlapScheme K σ)
    (hg : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) σ)
      (incidenceChartPoint K (g ≫ incidenceOverlapι K σ)).1)) :
    incidenceChartPoint K (g ≫ incidenceOverlapOtherι K σ) =
      incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) σ)
        (incidenceChartPoint K (g ≫ incidenceOverlapι K σ)) hg := by
  rw [incidenceChartPoint_other]
  exact incidencePointTransition_map_of_eq (affineFunctionHom g) σ (incidenceOverlapUniversal K σ) _
    (incidenceChartPoint_overlap K σ g).symm (incidenceOverlapUniversal_bijective K σ) hg

end
end PfaffianDescent

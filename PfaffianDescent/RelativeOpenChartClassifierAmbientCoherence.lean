import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterOverlap
import PfaffianDescent.RelativeOpenContainedFiniteFlatFunctor315

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false
variable {X B : Scheme.{u}} (F : X ⟶ B) (U : X.Opens) (n : ℕ) [IsSeparated F]
variable (H : Over B)
variable (eta : relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n ≅ yoneda.obj H)

/-- EVERY actual slice map preserves the classified entire ambient family. -/
theorem relativeOpenChartClassifiedAmbientPoint_natural001
    {T0 T1 : Over B} (a : T0 ⟶ T1) (g : T1 ⟶ H) :
    relativeOpenChartClassifiedAmbientPoint001 F U n H eta T0 (a ≫ g) =
      (relativeFiniteFlatHilbertFunctor197 F n).map a.op
        (relativeOpenChartClassifiedAmbientPoint001 F U n H eta T1 g) := by
  have h := ConcreteCategory.congr_hom (eta.inv.naturality a.op) g
  change eta.inv.app (.op T0) (a ≫ g) =
    (relativeFiniteFlatHilbertFunctor197 (U.ι ≫ F) n).map a.op
      (eta.inv.app (.op T1) g) at h
  change relativeOpenFiniteFlatPointPush315 U F n T0 (eta.inv.app (.op T0) (a ≫ g)) = _
  rw [h]
  exact relativeOpenFiniteFlatPointPush_natural315 U F n a (eta.inv.app (.op T1) g)

/-- The classified family lies in its OWN original chart, as an entire
source. The actual original projection diagram derives this membership. -/
theorem relativeOpenChartClassifiedAmbientPoint_entireSource_in_ownChart001
    (T : Over B) (g : T ⟶ H) :
    Set.range (relativeOpenChartClassifiedAmbientPoint001 F U n H eta T g).val.subschemeι ⊆
      (pullback.snd T.hom F ⁻¹ᵁ U : (pullback T.hom F).Opens) := by
  have hRange := ((relativeOpenContainedPointEquiv315 U F n T)
    (eta.inv.app (.op T) g)).property
  have hIdeal :
      ((relativeOpenContainedPointEquiv315 U F n T) (eta.inv.app (.op T) g)).val.val =
        (relativeOpenFiniteFlatPointPush315 U F n T (eta.inv.app (.op T) g)).val :=
    congrArg Subtype.val (relativeOpenContainedPointEquiv_push315 U F n T (eta.inv.app (.op T) g))
  change Set.range (((relativeOpenContainedPointEquiv315 U F n T)
    (eta.inv.app (.op T) g)).val.val).subschemeι ⊆
      Set.range (relativeClosedAmbientTestMap313 U.ι F T) at hRange
  rw [hIdeal] at hRange
  intro x hx
  obtain ⟨z, hz⟩ := hRange hx
  have hProjection : pullback.snd T.hom F
      (relativeClosedAmbientTestMap313 U.ι F T z) =
        U.ι (pullback.snd T.hom (U.ι ≫ F) z) :=
    congrArg (fun f => f z) (relativeClosedAmbientTestMap_toOriginal313 U.ι F T)
  change pullback.snd T.hom F x ∈ U
  rw [← hz, hProjection]
  exact (pullback.snd T.hom (U.ι ≫ F) z).property

/-- Whole ambient family equality determines the original classifier map,
by native315 injection and the constructed classifier's inverse law. -/
theorem relativeOpenChartClassifiedAmbientPoint_injective001 (T : Over B) :
    Function.Injective (relativeOpenChartClassifiedAmbientPoint001 F U n H eta T) := by
  intro g h heq
  have hi : eta.inv.app (.op T) g = eta.inv.app (.op T) h :=
    relativeOpenFiniteFlatPointPush_injective315 U F n T heq
  have hg : eta.hom.app (.op T) (eta.inv.app (.op T) g) = g :=
    ConcreteCategory.congr_hom (eta.inv_hom_id_app (.op T)) g
  have hh : eta.hom.app (.op T) (eta.inv.app (.op T) h) = h :=
    ConcreteCategory.congr_hom (eta.inv_hom_id_app (.op T)) h
  exact hg.symm.trans ((congrArg (fun P => eta.hom.app (.op T) P) hi).trans hh)

end PfaffianDescent
end

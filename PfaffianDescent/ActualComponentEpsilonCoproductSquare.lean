import PfaffianDescent.ActualSameComponentFrameEpsilonTransfer
import AllCharacteristics.FiniteSigmaSpec

/-! SOURCE ONLY, UNVERIFIED. Assemble the derived epsilon comparison on the
SAME four source components into the true product-dual scheme square. The
actual original whole-Z consumer uses its internally derived coproduct iso. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]

noncomputable def actualComponentProductDualIso
    (Z : Fin 4 → Scheme.{u}) (e : ∀ i, Z i ≅ Spec (.of (DualNumber K))) :
    (∐ Z) ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)) := by
  letI : IsIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K))) :=
    AllCharacteristics.isIso_sigmaSpec_const_finite (Fin 4) (DualNumber K)
  exact Sigma.mapIso e ≪≫ asIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K)))

theorem actualComponentProductDualIso_component
    (Z : Fin 4 → Scheme.{u}) (e : ∀ i, Z i ≅ Spec (.of (DualNumber K))) (i : Fin 4) :
    Sigma.ι Z i ≫ (actualComponentProductDualIso Z e).hom =
      (e i).hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) i)) := by
  unfold actualComponentProductDualIso
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc (Sigma.ι Z i), Sigma.ι_mapIso_hom]
  simp only [Category.assoc]
  rw [ι_sigmaSpec]

theorem actual_component_epsilon_coproduct_square
    (Z : Fin 4 → Scheme.{u})
    (canonicalE suppliedE : ∀ i, Z i ≅ Spec (.of (DualNumber K)))
    (epsilon : Fin 4 → K) (hepsilon : ∀ i, epsilon i ≠ 0)
    (hSquares : ∀ i, (suppliedE i).hom ≫ Spec.map (CommRingCat.ofHom
      (QuarticNet.dualNumberRescaleEquiv (epsilon i) (hepsilon i)).toRingHom) =
        (canonicalE i).hom) :
    (actualComponentProductDualIso Z suppliedE).hom ≫
      Spec.map (CommRingCat.ofHom
        (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom) =
    (actualComponentProductDualIso Z canonicalE).hom := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, actualComponentProductDualIso_component,
    actualComponentProductDualIso_component]
  have hNatural : CommRingCat.ofHom
        (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) i) =
    CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) i) ≫
      CommRingCat.ofHom (QuarticNet.dualNumberRescaleEquiv (epsilon i) (hepsilon i)).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact QuarticNet.fourTangentDualRescaleEquiv_apply epsilon hepsilon x i
  rw [Category.assoc, ← Spec.map_comp, hNatural, Spec.map_comp,
    ← Category.assoc, hSquares]

/-- The whole scheme is the actual source Q; w is supplied by the checked
closed-components/rank-eight coproduct factory, not a paper-facing certificate. -/
theorem actual_component_epsilon_original_whole_source_square
    (Z : Fin 4 → Scheme.{u}) {Q : Scheme.{u}} (w : (∐ Z) ≅ Q)
    (canonicalE suppliedE : ∀ i, Z i ≅ Spec (.of (DualNumber K)))
    (epsilon : Fin 4 → K) (hepsilon : ∀ i, epsilon i ≠ 0)
    (hSquares : ∀ i, (suppliedE i).hom ≫ Spec.map (CommRingCat.ofHom
      (QuarticNet.dualNumberRescaleEquiv (epsilon i) (hepsilon i)).toRingHom) =
        (canonicalE i).hom) :
    ((w.symm ≪≫ actualComponentProductDualIso Z suppliedE).hom) ≫
      Spec.map (CommRingCat.ofHom
        (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom) =
    (w.symm ≪≫ actualComponentProductDualIso Z canonicalE).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [actual_component_epsilon_coproduct_square Z canonicalE suppliedE epsilon hepsilon hSquares]

end PfaffianDescent

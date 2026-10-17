import PfaffianDescent.SchemeModuleFinitePointSequenceBalance
import PfaffianDescent.SchemeModuleLocallyRankOneTensor
import AllCharacteristics.HomogeneousProjective
import PfaffianDescent.CubicClosedDegreeElevenPointSerreExtension

/-! Bounded native section existence and literal equation transport.  The
transport moves the entire coefficient/section/base-action proposition,
rather than transporting only its numerical finranks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Opposite
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A positive native H0-minus-H1 Euler number forces a nonzero section
of this very coefficient.  No section or rank positivity is an input. -/
theorem schemeModule_exists_nonzero_top_section_of_positiveEuler230
    {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    0 < (Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
      Module.finrank K (schemeModuleCohomology X M 1) →
    ∃ s : M.val.obj (op ⊤), s ≠ 0 := by
  classical
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  intro hEuler
  have h0pos : 0 < Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) := by
    omega
  letI : Nontrivial (SchemeModuleOpenSectionsOver pi M ⊤) :=
    Module.nontrivial_of_finrank_pos h0pos
  obtain ⟨s, hs⟩ := exists_ne (0 : SchemeModuleOpenSectionsOver pi M ⊤)
  exact ⟨s, hs⟩

/-- Equality of equations transports the actual module, its original
section, H1 and independently defined original scalar action together.
Homogeneous witnesses are proof-irrelevant. -/
theorem planeCubicEquation_positiveEulerSectionProperty_transport230
    (p q : MvPolynomial (Fin 3) K) (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (heq : p = q) :
    (let X := hypersurface p hp
     let pi := hypersurfaceToBase p hp
     letI : HasExt.{u} X.Modules := schemeModules_hasExt X
     letI : Linear K X.Modules := schemeModulesLinearOver pi
     ∀ M : X.Modules, schemeModuleLocallyRankOne M →
       ∀ s : M.val.obj (op ⊤), s ≠ 0 →
         0 < (Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
           Module.finrank K (schemeModuleCohomology X M 1) →
         Subsingleton (schemeModuleCohomology X M 1)) →
    (let X := hypersurface q hq
     let pi := hypersurfaceToBase q hq
     letI : HasExt.{u} X.Modules := schemeModules_hasExt X
     letI : Linear K X.Modules := schemeModulesLinearOver pi
     ∀ M : X.Modules, schemeModuleLocallyRankOne M →
       ∀ s : M.val.obj (op ⊤), s ≠ 0 →
         0 < (Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) : ℤ) -
           Module.finrank K (schemeModuleCohomology X M 1) →
         Subsingleton (schemeModuleCohomology X M 1)) := by
  subst q
  exact fun h => h

end PfaffianDescent.Coray

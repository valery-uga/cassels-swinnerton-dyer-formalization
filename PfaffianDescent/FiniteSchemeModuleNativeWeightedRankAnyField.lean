import PfaffianDescent.SchemeModuleFiniteClosedSupportOriginalBaseGerms
import PfaffianDescent.IntrinsicFiniteCycle
import Mathlib.RingTheory.Length

/-! Source only. Native weighted germs on the entire finite scheme, retaining
the structural morphism's original scalar action. The length-comparison lemma
is an intermediate assembly cut; the positive-twist caller derives its local
input from actual homogeneous multiplication, without a supplied frame. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace AllCharacteristics
open scoped BigOperators
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finiteness over the original field makes every literal structure stalk
Artinian. This retains the entire local ring, including nilpotents. -/
theorem finiteScheme_nativeStalk_isArtinian_anyField
    (g : X ⟶ Spec (.of K)) [IsFinite g] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  letI : IsAffine X := isAffine_of_isAffineHom g
  letI := PfaffianDescent.finiteSchemeCoefficientAlgebra g
  letI : Module.Finite K Γ(X, ⊤) := PfaffianDescent.finiteSchemeCoefficient_finite g
  letI : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower K inferInstance
  let q : PrimeSpectrum Γ(X, ⊤) := X.isoSpec.hom x
  letI : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
    IsArtinianRing.localization_artinian q.asIdeal.primeCompl _
  letI : IsArtinianRing ((Spec (.of Γ(X, ⊤))).presheaf.stalk q) :=
    (Spec.stalkIso (.of Γ(X, ⊤)) q).commRingCatIsoToRingEquiv.symm.isArtinianRing
  exact (asIso (X.isoSpec.hom.stalkMap x)).commRingCatIsoToRingEquiv.isArtinianRing

/-- The original native global rank follows from the actual local length
comparison by the proved original-field germ decomposition. No global section
finiteness or global rank is assumed. The actual twist caller below constructs
the local comparison internally. -/
theorem finiteSchemeModuleTopSections_finite_and_nativeRank_of_stalkLength_anyField
    (g : X ⟶ Spec (.of K)) [IsFinite g] (M : X.Modules)
    (hLength : ∀ x : X,
      Module.length (X.presheaf.stalk x) ((schemeModuleStalkModuleFunctor X x).obj M) =
        Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    Module.Finite K (SchemeModuleOpenSectionsOver g M ⊤) ∧
      Module.finrank K (SchemeModuleOpenSectionsOver g M ⊤) = finiteSchemeRank g := by
  classical
  letI := PfaffianDescent.finiteScheme_isArtinian g
  let C : Set X := Set.univ
  have hC : C.Finite := Set.toFinite C
  letI : Fintype C := hC.fintype
  letI : Fintype (closedPoints X) := Fintype.ofFinite _
  have hclosed : ∀ x ∈ C, IsClosed ({x} : Set X) := fun _ _ => isClosed_singleton
  have hlocal : ∀ x : C, IsFiniteLength (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj M) := by
    intro x
    letI := finiteScheme_nativeStalk_isArtinian_anyField g x.1
    apply Module.length_ne_top_iff.mp
    rw [hLength x.1]
    exact Module.length_ne_top
  have h := schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
    g M C hC hclosed (fun _ _ => Set.mem_univ _) hlocal
  let e : closedPoints X ≃ C :=
    { toFun := fun x => ⟨x.1, Set.mem_univ x.1⟩
      invFun := fun x => ⟨x.1, isClosed_singleton⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    (∑ x : C, (Module.length (X.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor X x.1).obj M)).toNat * g.residueDegree x.1) =
        ∑ x : C, (Module.length (X.presheaf.stalk x.1)
          (X.presheaf.stalk x.1)).toNat * g.residueDegree x.1 := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg₂ Nat.mul (congrArg ENat.toNat (hLength x.1)) rfl
    _ = ∑ x : closedPoints X, (Module.length (X.presheaf.stalk x.1)
        (X.presheaf.stalk x.1)).toNat * g.residueDegree x.1 :=
      (e.sum_comp (fun x : C => (Module.length (X.presheaf.stalk x.1)
        (X.presheaf.stalk x.1)).toNat * g.residueDegree x.1)).symm
    _ = EffectiveZeroCycle.degree g (PfaffianDescent.finiteSchemeFundamentalCycle g) :=
      (fundamentalZeroCycle_degree_eq_sum g).symm
    _ = finiteSchemeRank g := PfaffianDescent.finiteSchemeFundamentalCycle_degree g

end PfaffianDescent.Coray

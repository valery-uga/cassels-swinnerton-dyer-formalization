import PfaffianDescent.ActualAffineConormalNativeSectionClass
import PfaffianDescent.ActualAffineGenuineDifferentialForwardPointMap
import PfaffianDescent.ActualAffineGlobalConormalAdjunctionAction

/- SOURCE ONLY / UNVERIFIED. Forward-defined actual conormal map and its
comparison with the genuine GLOBAL conormal map. Existing inverse-defined
fiber maps/equivalences are untouched. No comparison, generation or
quasicoherence certificate is a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open IdealSheafDataModule BundleSectionZeroLocus
open scoped TensorProduct
universe u
variable {k R L : Type u} [CommRing k] [CommRing R] [Field L] [Algebra k R]

private lemma actualForwardAffineModulePointClass_top
    (rho : R →+* L) (M : (Spec (.of R)).Modules)
    (t : schemeModuleUnit (Spec (.of R)) ⟶ M) :
    actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho)) M t =
    actualAffineSheafPointClass (CommRingCat.ofHom rho) M
      (t.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤))) := by
  rw [actualAffineModulePointSectionClass_eq_evaluation]
  rfl

private lemma actualForwardNativeIdealTopCoefficient
    (rho : R →+* L) [IsClosedImmersion (Spec.map (CommRingCat.ofHom rho))]
    (x : RingHom.ker rho) :
    (closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom rho))).val.app (op ⊤)
      ((cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x).val.app
        (op ⊤) (1 : Γ(Spec (.of R), ⊤))) =
      (Scheme.ΓSpecIso (.of R)).inv.hom x.1 := by
  have h := congrArg (fun f => f.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤)))
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom_toUnit rho x)
  exact h.trans (unitEndomorphismValue_ofRegularFunction (X := Spec (.of R))
    ((affineGlobalSectionsUnitLinearEquiv (A := R)).symm x.1))

/-- Forward construction into the SAME genuinely sheafified differential fiber. -/
def actualAffineForwardConormalDifferentialFiberMap
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toAlgebra
    (moduleSpecΓFunctor (R := .of L)).obj
        (actualClosedImmersionConormalModule (Spec.map (CommRingCat.ofHom rho))) →ₗ[L]
      (moduleSpecΓFunctor (R := .of L)).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
          (schemeRelativeDifferentials
            (Spec.map (CommRingCat.ofHom (algebraMap k R))))) := by
  letI : Algebra R L := rho.toAlgebra
  exact (actualAffineGenuineDifferentialForwardPointMap (k := k) rho).comp
    ((LinearMap.liftBaseChange L (KaehlerDifferential.kerToTensor k R L)).comp
      (actualAffineConormalTensorEquiv rho hrho).toLinearMap)

lemma actualAffineForwardConormalDifferentialFiberMap_nativeSection
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    actualAffineForwardConormalDifferentialFiberMap (k := k) rho hrho
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) =
    actualAffineSheafPointClass (CommRingCat.ofHom rho)
      (schemeRelativeDifferentials
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
        ((Scheme.ΓSpecIso (.of R)).inv.hom x.1)) := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  let q := Spec.map (CommRingCat.ofHom rho)
  let J : (Spec (.of R)).Modules := closedImmersionModule q
  let s : schemeModuleUnit (Spec (.of R)) ⟶ J :=
    cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x
  let O : (Spec (.of R)).Modules := schemeRelativeDifferentials
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  let G := moduleSpecΓFunctor (R := .of L)
  let N : ModuleCat L := G.obj (actualClosedImmersionConormalModule q)
  let c : N := actualModulePointSectionClass q J s
  let E : N ≃ₗ[L] L ⊗[R] RingHom.ker rho :=
    actualAffineConormalTensorEquiv rho hrho
  let b : L ⊗[R] RingHom.ker rho →ₗ[L] L ⊗[R] KaehlerDifferential k R :=
    LinearMap.liftBaseChange L (KaehlerDifferential.kerToTensor k R L)
  let F : L ⊗[R] KaehlerDifferential k R →ₗ[L]
      G.obj ((Scheme.Modules.pullback q).obj O) :=
    actualAffineGenuineDifferentialForwardPointMap (k := k) rho
  have hE : E c = (1 : L) ⊗ₜ[R] x :=
    actualAffineConormalTensorEquiv_nativeSection rho hrho x
  have hker : KaehlerDifferential.kerToTensor k R L x =
      (1 : L) ⊗ₜ[R] KaehlerDifferential.D k R x.1 := rfl
  have hb : b ((1 : L) ⊗ₜ[R] x) =
      (1 : L) ⊗ₜ[R] KaehlerDifferential.D k R x.1 :=
    (LinearMap.liftBaseChange_one_tmul L
      (KaehlerDifferential.kerToTensor k R L) x).trans hker
  have hF : F ((1 : L) ⊗ₜ[R] KaehlerDifferential.D k R x.1) =
      actualAffineSheafPointClass (CommRingCat.ofHom rho) O
        (actualRelativeDifferentialSection
          (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤
          ((Scheme.ΓSpecIso (.of R)).inv.hom x.1)) :=
    actualAffineGenuineDifferentialForwardPointMap_one_tmul_D (k := k) rho x.1
  change F (b (E c)) = _
  exact (congrArg (fun t : L ⊗[R] RingHom.ker rho => F (b t)) hE).trans
    ((congrArg (fun t : L ⊗[R] KaehlerDifferential k R => F t) hb).trans hF)

lemma actualAffineGlobalConormalForwardMap_nativeSection
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom rho)))
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) =
    actualAffineForwardConormalDifferentialFiberMap (k := k) rho hrho
      (actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
        (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
        (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x)) := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  let J := closedImmersionModule (Spec.map (CommRingCat.ofHom rho))
  let s := cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x
  let d := (moduleSpecΓFunctor (R := .of L)).map
    (actualGlobalClosedConormalDifferentialMap
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map (CommRingCat.ofHom rho)))
  have he := actualForwardAffineModulePointClass_top rho J s
  have ha := actualAffineGlobalConormalAdjunctionAction (k := k) rho
    (s.val.app (op ⊤) (1 : Γ(Spec (.of R), ⊤)))
  have hc := actualForwardNativeIdealTopCoefficient rho x
  have hvalue := congrArg
    (fun r => actualAffineSheafPointClass (CommRingCat.ofHom rho)
      (schemeRelativeDifferentials
        (Spec.map (CommRingCat.ofHom (algebraMap k R))))
      (actualRelativeDifferentialSection
        (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⊤ r)) hc
  exact ((congrArg (fun z => d z) he).trans ha).trans
    (hvalue.trans
      (actualAffineForwardConormalDifferentialFiberMap_nativeSection
        (k := k) rho hrho x).symm)

/-- Full equality of actual L-linear maps. Native tensor coordinates internally
supply all generators; no generation or desired comparison input is required. -/
lemma actualAffineGlobalConormalForwardFiberComparison
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toAlgebra
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
      IsClosedImmersion.spec_of_surjective _ hrho
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap
        (Spec.map (CommRingCat.ofHom (algebraMap k R)))
        (Spec.map (CommRingCat.ofHom rho)))).hom =
      actualAffineForwardConormalDifferentialFiberMap (k := k) rho hrho := by
  dsimp only
  letI : Algebra R L := rho.toAlgebra
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom rho)) :=
    IsClosedImmersion.spec_of_surjective _ hrho
  let E := actualAffineConormalTensorEquiv rho hrho
  let D := ((moduleSpecΓFunctor (R := .of L)).map
    (actualGlobalClosedConormalDifferentialMap
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map (CommRingCat.ofHom rho)))).hom
  let F := actualAffineForwardConormalDifferentialFiberMap (k := k) rho hrho
  have h : ∀ t : L ⊗[R] RingHom.ker rho, D (E.symm t) = F (E.symm t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      have he : E.symm ((1 : L) ⊗ₜ[R] x) =
          actualModulePointSectionClass (Spec.map (CommRingCat.ofHom rho))
            (closedImmersionModule (Spec.map (CommRingCat.ofHom rho)))
            (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom rho x) := by
        apply E.injective
        rw [E.apply_symm_apply, actualAffineConormalTensorEquiv_nativeSection]
      have ht : a ⊗ₜ[R] x = a • ((1 : L) ⊗ₜ[R] x) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, E.symm.map_smul, D.map_smul, F.map_smul, he]
      exact congrArg (fun z => a • z)
        (actualAffineGlobalConormalForwardMap_nativeSection (k := k) rho hrho x)
    | add t s ht hs => simp only [map_add, ht, hs]
  apply LinearMap.ext
  intro z
  simpa only [E.symm_apply_apply] using h (E z)

end PfaffianDescent

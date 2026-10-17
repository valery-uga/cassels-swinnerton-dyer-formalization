import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCanonicalPlane
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeBasisMatrix

/-! # The actual Serre evaluation minor identifies its actual incidence with a plane -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceNativeSerre_exists_plane
    {K : Type u} [Field K] {X B : Scheme.{u}} [IsAffine B] {N : X.Modules}
    (base : X ⟶ Spec (.of K)) [IsSeparated base] (e : SerreExtensionData X N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E))]
    (h9 : Module.finrank K (SchemeModuleGlobalSectionsOver base (show X.Modules from e.E)) = 9)
    (b : B ⟶ Spec (.of K)) (chart : Fin 3 → C.ι)
    (markedU : ∀ i, B ⟶ (C.U (chart i) : Scheme.{u}))
    (hmarked : ∀ i, (markedU i ≫ (C.U (chart i)).ι) ≫ base = b)
    (m : (Fin 3 × ULift.{u} (Fin 2)) ↪ Fin 9)
    (hm : IsUnit ((serreIncidenceNativeAffineEvaluationMatrix
      base e C h9 chart markedU).submatrix id m).det) :
    let D := serreIncidenceRankTwoAffineCover e C
    letI := D.isClosedImmersion_projectiveSectionLocalZeroGluedToAmbient base
      (show X.Modules from e.E)
    let I := serreThreePointSectionIncidenceIdeal b base
      (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E))
      (fun i => markedU i ≫ (C.U (chart i)).ι) hmarked
      (D.projectiveSectionLocalZeroGluedToAmbient base (show X.Modules from e.E))
    ∃ v : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅
        I.subscheme,
      v.hom ≫ I.subschemeι ≫ pullback.fst b
        (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E)) =
        toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫
          B.isoSpec.inv ∧
      IsOpenMap (I.subschemeι ≫ pullback.fst b
        (schemeModuleGlobalSectionsProjectiveParametersToBase base (show X.Modules from e.E))) := by
  let ρ : Fin 6 ≃ (Fin 3 × ULift.{u} (Fin 2)) := Fintype.equivOfCardEq (by simp)
  let m' : Fin 6 ↪ Fin 9 := ρ.toEmbedding.trans m
  let A := serreIncidenceNativeAffineEvaluationMatrix base e C h9 chart markedU
  have hA : (fun r k => serreIncidenceGlobalBasisEvaluationMatrix base
      (show X.Modules from e.E) (serreIncidenceRankTwoAffineCover e C) chart markedU
        (ρ r) ((finCongr h9).symm k)) = A.submatrix ρ id := by
    funext r k
    exact serreIncidenceGlobalBasisEvaluationMatrix_eq_native base e C h9 chart markedU (ρ r) k
  have hd : (Matrix.submatrix (fun r k => serreIncidenceGlobalBasisEvaluationMatrix base
      (show X.Modules from e.E) (serreIncidenceRankTwoAffineCover e C) chart markedU
        (ρ r) ((finCongr h9).symm k)) id m').det = (A.submatrix id m).det := by
    rw [hA]
    change ((A.submatrix id m).submatrix ρ ρ).det = _
    exact Matrix.det_submatrix_equiv_self ρ (A.submatrix id m)
  have hm' := hd.symm ▸ hm
  exact serreThreePointSectionIncidence_exists_native_plane base (show X.Modules from e.E)
    (serreIncidenceRankTwoAffineCover e C) b chart markedU hmarked h9 ρ m' hm'

end PfaffianDescent

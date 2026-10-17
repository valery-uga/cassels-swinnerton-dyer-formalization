import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedFamily

/-! # Literal marked morphisms into the actual incidence zero family -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
variable {S B X P Z : Scheme.{u}}
variable (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S)
variable (marked : Fin 3 → (B ⟶ X)) (hmarked : ∀ i, marked i ≫ x = b)
variable (zero : Z ⟶ pullback x p) [IsClosedImmersion zero]

/-- Each marked incidence equation supplies an actual scheme morphism into
the original universal zero scheme, via the literal quotient inclusion. -/
def serreIncidenceMarkedToUniversalZero (i : Fin 3) :
    serreThreePointSectionIncidence b x p marked hmarked zero ⟶ Z :=
  Scheme.IdealSheafData.inclusion
    (show zero.ker.comap (fixedLinearSystemIncidenceMap b x p marked hmarked i) ≤
      serreThreePointSectionIncidenceIdeal b x p marked hmarked zero from
        le_iSup (fun j : Fin 3 => zero.ker.comap
          (fixedLinearSystemIncidenceMap b x p marked hmarked j)) i) ≫
    (zero.ker.comapIso (fixedLinearSystemIncidenceMap b x p marked hmarked i)).hom ≫
    pullback.snd (fixedLinearSystemIncidenceMap b x p marked hmarked i) zero.ker.subschemeι ≫
    inv zero.toImage

@[reassoc] theorem serreIncidenceMarkedToUniversalZero_comp (i : Fin 3) :
    serreIncidenceMarkedToUniversalZero b x p marked hmarked zero i ≫ zero =
      serreThreePointSectionIncidenceToProduct b x p marked hmarked zero ≫
        fixedLinearSystemIncidenceMap b x p marked hmarked i := by
  have hinv : inv zero.toImage ≫ zero = zero.imageι := by
    calc
      inv zero.toImage ≫ zero = inv zero.toImage ≫ (zero.toImage ≫ zero.imageι) :=
        congrArg (fun f => inv zero.toImage ≫ f) zero.toImage_imageι.symm
      _ = zero.imageι := by simp
  unfold serreIncidenceMarkedToUniversalZero
  simp only [Category.assoc, hinv]
  rw [← pullback.condition]
  simp only [Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    Scheme.IdealSheafData.inclusion_subschemeι_assoc]

@[reassoc] theorem serreIncidenceMarkedToUniversalZero_toParameters (i : Fin 3) :
    serreIncidenceMarkedToUniversalZero b x p marked hmarked zero i ≫
      (zero ≫ pullback.snd x p) =
        serreThreePointSectionIncidenceToParameters b x p marked hmarked zero := by
  rw [← Category.assoc, serreIncidenceMarkedToUniversalZero_comp, Category.assoc,
    fixedLinearSystemIncidenceMap_snd]

/-- The marked universal-zero morphism and the identity on incidence give a
literal section of the pulled-back zero family over incidence. -/
def serreIncidenceMarkedZeroSection (i : Fin 3) :
    serreThreePointSectionIncidence b x p marked hmarked zero ⟶
      pullback (zero ≫ pullback.snd x p)
        (serreThreePointSectionIncidenceToParameters b x p marked hmarked zero) :=
  pullback.lift (serreIncidenceMarkedToUniversalZero b x p marked hmarked zero i)
    (𝟙 _) (by
      rw [Category.id_comp]
      exact serreIncidenceMarkedToUniversalZero_toParameters b x p marked hmarked zero i)

@[reassoc] theorem serreIncidenceMarkedZeroSection_toIncidence (i : Fin 3) :
    serreIncidenceMarkedZeroSection b x p marked hmarked zero i ≫
      serreThreePointSectionIncidenceZeroFamily b x p marked hmarked zero = 𝟙 _ :=
  pullback.lift_snd _ _ _

end PfaffianDescent

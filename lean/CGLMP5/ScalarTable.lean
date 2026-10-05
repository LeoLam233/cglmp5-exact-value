import CGLMP5.ScalarTableRow00
import CGLMP5.ScalarTableRow01
import CGLMP5.ScalarTableRow02
import CGLMP5.ScalarTableRow03
import CGLMP5.ScalarTableRow04
import CGLMP5.ScalarTableRow05
import CGLMP5.ScalarTableRow06
import CGLMP5.ScalarTableRow07
import CGLMP5.ScalarTableRow08
import CGLMP5.ScalarTableRow09
import CGLMP5.ScalarTableRow10
import CGLMP5.ScalarTableRow11
import CGLMP5.ScalarTableRow12
import CGLMP5.ScalarTableRow13
import CGLMP5.ScalarTableRow14
import CGLMP5.ScalarTableRow15
import CGLMP5.ScalarTableRow16
import CGLMP5.ScalarTableRow17
import CGLMP5.ScalarTableRow18
import CGLMP5.ScalarTableRow19
import CGLMP5.ScalarTableRow20
import CGLMP5.ScalarTableRow21
import CGLMP5.ScalarTableRow22
import CGLMP5.ScalarTableRow23

namespace CGLMP5.Scalar

lemma mulCoeff_sound (i j : Fin 24) :
    (∑ k : Fin 24, (mulCoeff i j k : ℂ)*basisEval k) = basisEval i* basisEval j := by
  fin_cases i
  · exact mulCoeff_sound_row_0 j
  · exact mulCoeff_sound_row_1 j
  · exact mulCoeff_sound_row_2 j
  · exact mulCoeff_sound_row_3 j
  · exact mulCoeff_sound_row_4 j
  · exact mulCoeff_sound_row_5 j
  · exact mulCoeff_sound_row_6 j
  · exact mulCoeff_sound_row_7 j
  · exact mulCoeff_sound_row_8 j
  · exact mulCoeff_sound_row_9 j
  · exact mulCoeff_sound_row_10 j
  · exact mulCoeff_sound_row_11 j
  · exact mulCoeff_sound_row_12 j
  · exact mulCoeff_sound_row_13 j
  · exact mulCoeff_sound_row_14 j
  · exact mulCoeff_sound_row_15 j
  · exact mulCoeff_sound_row_16 j
  · exact mulCoeff_sound_row_17 j
  · exact mulCoeff_sound_row_18 j
  · exact mulCoeff_sound_row_19 j
  · exact mulCoeff_sound_row_20 j
  · exact mulCoeff_sound_row_21 j
  · exact mulCoeff_sound_row_22 j
  · exact mulCoeff_sound_row_23 j

end CGLMP5.Scalar

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import CGLMP5.SOSCompressedCheck00
import CGLMP5.SOSCompressedCheck01
import CGLMP5.SOSCompressedCheck02
import CGLMP5.SOSCompressedCheck03
import CGLMP5.SOSCompressedCheck04
import CGLMP5.SOSCompressedCheck05
import CGLMP5.SOSCompressedCheck06
import CGLMP5.SOSCompressedCheck07
import CGLMP5.SOSCompressedCheck08
import CGLMP5.SOSCompressedCheck09
import CGLMP5.SOSCompressedCheck10
import CGLMP5.SOSCompressedCheck11
import CGLMP5.SOSCompressedCheck12
import CGLMP5.SOSCompressedCheck13

namespace CGLMP5.SOSFinite

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem gram_pair_checked (h : Fin 135) :
    Scalar.mul (Scalar.conj (core (gramOrigin h).2.1)) (core (gramOrigin h).2.2) = gramPair h := by
  funext k
  fin_cases h
  · exact gram_pair_0 k
  · exact gram_pair_1 k
  · exact gram_pair_2 k
  · exact gram_pair_3 k
  · exact gram_pair_4 k
  · exact gram_pair_5 k
  · exact gram_pair_6 k
  · exact gram_pair_7 k
  · exact gram_pair_8 k
  · exact gram_pair_9 k
  · exact gram_pair_10 k
  · exact gram_pair_11 k
  · exact gram_pair_12 k
  · exact gram_pair_13 k
  · exact gram_pair_14 k
  · exact gram_pair_15 k
  · exact gram_pair_16 k
  · exact gram_pair_17 k
  · exact gram_pair_18 k
  · exact gram_pair_19 k
  · exact gram_pair_20 k
  · exact gram_pair_21 k
  · exact gram_pair_22 k
  · exact gram_pair_23 k
  · exact gram_pair_24 k
  · exact gram_pair_25 k
  · exact gram_pair_26 k
  · exact gram_pair_27 k
  · exact gram_pair_28 k
  · exact gram_pair_29 k
  · exact gram_pair_30 k
  · exact gram_pair_31 k
  · exact gram_pair_32 k
  · exact gram_pair_33 k
  · exact gram_pair_34 k
  · exact gram_pair_35 k
  · exact gram_pair_36 k
  · exact gram_pair_37 k
  · exact gram_pair_38 k
  · exact gram_pair_39 k
  · exact gram_pair_40 k
  · exact gram_pair_41 k
  · exact gram_pair_42 k
  · exact gram_pair_43 k
  · exact gram_pair_44 k
  · exact gram_pair_45 k
  · exact gram_pair_46 k
  · exact gram_pair_47 k
  · exact gram_pair_48 k
  · exact gram_pair_49 k
  · exact gram_pair_50 k
  · exact gram_pair_51 k
  · exact gram_pair_52 k
  · exact gram_pair_53 k
  · exact gram_pair_54 k
  · exact gram_pair_55 k
  · exact gram_pair_56 k
  · exact gram_pair_57 k
  · exact gram_pair_58 k
  · exact gram_pair_59 k
  · exact gram_pair_60 k
  · exact gram_pair_61 k
  · exact gram_pair_62 k
  · exact gram_pair_63 k
  · exact gram_pair_64 k
  · exact gram_pair_65 k
  · exact gram_pair_66 k
  · exact gram_pair_67 k
  · exact gram_pair_68 k
  · exact gram_pair_69 k
  · exact gram_pair_70 k
  · exact gram_pair_71 k
  · exact gram_pair_72 k
  · exact gram_pair_73 k
  · exact gram_pair_74 k
  · exact gram_pair_75 k
  · exact gram_pair_76 k
  · exact gram_pair_77 k
  · exact gram_pair_78 k
  · exact gram_pair_79 k
  · exact gram_pair_80 k
  · exact gram_pair_81 k
  · exact gram_pair_82 k
  · exact gram_pair_83 k
  · exact gram_pair_84 k
  · exact gram_pair_85 k
  · exact gram_pair_86 k
  · exact gram_pair_87 k
  · exact gram_pair_88 k
  · exact gram_pair_89 k
  · exact gram_pair_90 k
  · exact gram_pair_91 k
  · exact gram_pair_92 k
  · exact gram_pair_93 k
  · exact gram_pair_94 k
  · exact gram_pair_95 k
  · exact gram_pair_96 k
  · exact gram_pair_97 k
  · exact gram_pair_98 k
  · exact gram_pair_99 k
  · exact gram_pair_100 k
  · exact gram_pair_101 k
  · exact gram_pair_102 k
  · exact gram_pair_103 k
  · exact gram_pair_104 k
  · exact gram_pair_105 k
  · exact gram_pair_106 k
  · exact gram_pair_107 k
  · exact gram_pair_108 k
  · exact gram_pair_109 k
  · exact gram_pair_110 k
  · exact gram_pair_111 k
  · exact gram_pair_112 k
  · exact gram_pair_113 k
  · exact gram_pair_114 k
  · exact gram_pair_115 k
  · exact gram_pair_116 k
  · exact gram_pair_117 k
  · exact gram_pair_118 k
  · exact gram_pair_119 k
  · exact gram_pair_120 k
  · exact gram_pair_121 k
  · exact gram_pair_122 k
  · exact gram_pair_123 k
  · exact gram_pair_124 k
  · exact gram_pair_125 k
  · exact gram_pair_126 k
  · exact gram_pair_127 k
  · exact gram_pair_128 k
  · exact gram_pair_129 k
  · exact gram_pair_130 k
  · exact gram_pair_131 k
  · exact gram_pair_132 k
  · exact gram_pair_133 k
  · exact gram_pair_134 k

theorem gram_weight_checked (h : Fin 135) :
    Scalar.mul (CanonicalData.weight (gramOrigin h).1) (gramPair h) = gram h := by
  funext k
  fin_cases h
  · exact gram_weight_0 k
  · exact gram_weight_1 k
  · exact gram_weight_2 k
  · exact gram_weight_3 k
  · exact gram_weight_4 k
  · exact gram_weight_5 k
  · exact gram_weight_6 k
  · exact gram_weight_7 k
  · exact gram_weight_8 k
  · exact gram_weight_9 k
  · exact gram_weight_10 k
  · exact gram_weight_11 k
  · exact gram_weight_12 k
  · exact gram_weight_13 k
  · exact gram_weight_14 k
  · exact gram_weight_15 k
  · exact gram_weight_16 k
  · exact gram_weight_17 k
  · exact gram_weight_18 k
  · exact gram_weight_19 k
  · exact gram_weight_20 k
  · exact gram_weight_21 k
  · exact gram_weight_22 k
  · exact gram_weight_23 k
  · exact gram_weight_24 k
  · exact gram_weight_25 k
  · exact gram_weight_26 k
  · exact gram_weight_27 k
  · exact gram_weight_28 k
  · exact gram_weight_29 k
  · exact gram_weight_30 k
  · exact gram_weight_31 k
  · exact gram_weight_32 k
  · exact gram_weight_33 k
  · exact gram_weight_34 k
  · exact gram_weight_35 k
  · exact gram_weight_36 k
  · exact gram_weight_37 k
  · exact gram_weight_38 k
  · exact gram_weight_39 k
  · exact gram_weight_40 k
  · exact gram_weight_41 k
  · exact gram_weight_42 k
  · exact gram_weight_43 k
  · exact gram_weight_44 k
  · exact gram_weight_45 k
  · exact gram_weight_46 k
  · exact gram_weight_47 k
  · exact gram_weight_48 k
  · exact gram_weight_49 k
  · exact gram_weight_50 k
  · exact gram_weight_51 k
  · exact gram_weight_52 k
  · exact gram_weight_53 k
  · exact gram_weight_54 k
  · exact gram_weight_55 k
  · exact gram_weight_56 k
  · exact gram_weight_57 k
  · exact gram_weight_58 k
  · exact gram_weight_59 k
  · exact gram_weight_60 k
  · exact gram_weight_61 k
  · exact gram_weight_62 k
  · exact gram_weight_63 k
  · exact gram_weight_64 k
  · exact gram_weight_65 k
  · exact gram_weight_66 k
  · exact gram_weight_67 k
  · exact gram_weight_68 k
  · exact gram_weight_69 k
  · exact gram_weight_70 k
  · exact gram_weight_71 k
  · exact gram_weight_72 k
  · exact gram_weight_73 k
  · exact gram_weight_74 k
  · exact gram_weight_75 k
  · exact gram_weight_76 k
  · exact gram_weight_77 k
  · exact gram_weight_78 k
  · exact gram_weight_79 k
  · exact gram_weight_80 k
  · exact gram_weight_81 k
  · exact gram_weight_82 k
  · exact gram_weight_83 k
  · exact gram_weight_84 k
  · exact gram_weight_85 k
  · exact gram_weight_86 k
  · exact gram_weight_87 k
  · exact gram_weight_88 k
  · exact gram_weight_89 k
  · exact gram_weight_90 k
  · exact gram_weight_91 k
  · exact gram_weight_92 k
  · exact gram_weight_93 k
  · exact gram_weight_94 k
  · exact gram_weight_95 k
  · exact gram_weight_96 k
  · exact gram_weight_97 k
  · exact gram_weight_98 k
  · exact gram_weight_99 k
  · exact gram_weight_100 k
  · exact gram_weight_101 k
  · exact gram_weight_102 k
  · exact gram_weight_103 k
  · exact gram_weight_104 k
  · exact gram_weight_105 k
  · exact gram_weight_106 k
  · exact gram_weight_107 k
  · exact gram_weight_108 k
  · exact gram_weight_109 k
  · exact gram_weight_110 k
  · exact gram_weight_111 k
  · exact gram_weight_112 k
  · exact gram_weight_113 k
  · exact gram_weight_114 k
  · exact gram_weight_115 k
  · exact gram_weight_116 k
  · exact gram_weight_117 k
  · exact gram_weight_118 k
  · exact gram_weight_119 k
  · exact gram_weight_120 k
  · exact gram_weight_121 k
  · exact gram_weight_122 k
  · exact gram_weight_123 k
  · exact gram_weight_124 k
  · exact gram_weight_125 k
  · exact gram_weight_126 k
  · exact gram_weight_127 k
  · exact gram_weight_128 k
  · exact gram_weight_129 k
  · exact gram_weight_130 k
  · exact gram_weight_131 k
  · exact gram_weight_132 k
  · exact gram_weight_133 k
  · exact gram_weight_134 k

end CGLMP5.SOSFinite

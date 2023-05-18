Require Import Bool.
Require Import List.
Require Import lib.
Require Import prim.
Require Import tacdef.

Require Import 
rij_m_comm8_0   rij_m_comm8_1   rij_m_comm8_2   rij_m_comm8_3   rij_m_comm8_4   rij_m_comm8_5  
rij_m_comm8_6   rij_m_comm8_7   rij_m_comm8_8   rij_m_comm8_9   rij_m_comm8_10  rij_m_comm8_11 
rij_m_comm8_12  rij_m_comm8_13  rij_m_comm8_14  rij_m_comm8_15  rij_m_comm8_16  rij_m_comm8_17 
rij_m_comm8_18  rij_m_comm8_19  rij_m_comm8_20  rij_m_comm8_21  rij_m_comm8_22  rij_m_comm8_23 
rij_m_comm8_24  rij_m_comm8_25  rij_m_comm8_26  rij_m_comm8_27  rij_m_comm8_28  rij_m_comm8_29 
rij_m_comm8_30  rij_m_comm8_31  rij_m_comm8_32  rij_m_comm8_33  rij_m_comm8_34  rij_m_comm8_35 
rij_m_comm8_36  rij_m_comm8_37  rij_m_comm8_38  rij_m_comm8_39  rij_m_comm8_40  rij_m_comm8_41 
rij_m_comm8_42  rij_m_comm8_43  rij_m_comm8_44  rij_m_comm8_45  rij_m_comm8_46  rij_m_comm8_47 
rij_m_comm8_48  rij_m_comm8_49  rij_m_comm8_50  rij_m_comm8_51  rij_m_comm8_52  rij_m_comm8_53 
rij_m_comm8_54  rij_m_comm8_55  rij_m_comm8_56  rij_m_comm8_57  rij_m_comm8_58  rij_m_comm8_59 
rij_m_comm8_60  rij_m_comm8_61  rij_m_comm8_62  rij_m_comm8_63  rij_m_comm8_64  rij_m_comm8_65 
rij_m_comm8_66  rij_m_comm8_67  rij_m_comm8_68  rij_m_comm8_69  rij_m_comm8_70  rij_m_comm8_71
rij_m_comm8_72  rij_m_comm8_73  rij_m_comm8_74  rij_m_comm8_75  rij_m_comm8_76  rij_m_comm8_77 
rij_m_comm8_78  rij_m_comm8_79  rij_m_comm8_80  rij_m_comm8_81  rij_m_comm8_82  rij_m_comm8_83 
rij_m_comm8_84  rij_m_comm8_85  rij_m_comm8_86  rij_m_comm8_87  rij_m_comm8_88  rij_m_comm8_89 
rij_m_comm8_90  rij_m_comm8_91  rij_m_comm8_92  rij_m_comm8_93  rij_m_comm8_94  rij_m_comm8_95 
rij_m_comm8_96  rij_m_comm8_97  rij_m_comm8_98  rij_m_comm8_99  rij_m_comm8_100 rij_m_comm8_101 
rij_m_comm8_102 rij_m_comm8_103 rij_m_comm8_104 rij_m_comm8_105 rij_m_comm8_106 rij_m_comm8_107 
rij_m_comm8_108 rij_m_comm8_109 rij_m_comm8_110 rij_m_comm8_111 rij_m_comm8_112 rij_m_comm8_113 
rij_m_comm8_114 rij_m_comm8_115 rij_m_comm8_116 rij_m_comm8_117 rij_m_comm8_118 rij_m_comm8_119 
rij_m_comm8_120 rij_m_comm8_121 rij_m_comm8_122 rij_m_comm8_123 rij_m_comm8_124 rij_m_comm8_125 
rij_m_comm8_126 rij_m_comm8_127 rij_m_comm8_128 rij_m_comm8_129 rij_m_comm8_130 rij_m_comm8_131 
rij_m_comm8_132 rij_m_comm8_133 rij_m_comm8_134 rij_m_comm8_135 rij_m_comm8_136 rij_m_comm8_137 
rij_m_comm8_138 rij_m_comm8_139 rij_m_comm8_140 rij_m_comm8_141 rij_m_comm8_142 rij_m_comm8_143 
rij_m_comm8_144 rij_m_comm8_145 rij_m_comm8_146 rij_m_comm8_147 rij_m_comm8_148 rij_m_comm8_149 
rij_m_comm8_150 rij_m_comm8_151 rij_m_comm8_152 rij_m_comm8_153 rij_m_comm8_154 rij_m_comm8_155 
rij_m_comm8_156 rij_m_comm8_157 rij_m_comm8_158 rij_m_comm8_159 rij_m_comm8_160 rij_m_comm8_161 
rij_m_comm8_162 rij_m_comm8_163 rij_m_comm8_164 rij_m_comm8_165 rij_m_comm8_166 rij_m_comm8_167 
rij_m_comm8_168 rij_m_comm8_169 rij_m_comm8_170 rij_m_comm8_171 rij_m_comm8_172 rij_m_comm8_173 
rij_m_comm8_174 rij_m_comm8_175 rij_m_comm8_176 rij_m_comm8_177 rij_m_comm8_178 rij_m_comm8_179 
rij_m_comm8_180 rij_m_comm8_181 rij_m_comm8_182 rij_m_comm8_183 rij_m_comm8_184 rij_m_comm8_185 
rij_m_comm8_186 rij_m_comm8_187 rij_m_comm8_188 rij_m_comm8_189 rij_m_comm8_190 rij_m_comm8_191 
rij_m_comm8_192 rij_m_comm8_193 rij_m_comm8_194 rij_m_comm8_195 rij_m_comm8_196 rij_m_comm8_197 
rij_m_comm8_198 rij_m_comm8_199 rij_m_comm8_200 rij_m_comm8_201 rij_m_comm8_202 rij_m_comm8_203 
rij_m_comm8_204 rij_m_comm8_205 rij_m_comm8_206 rij_m_comm8_207 rij_m_comm8_208 rij_m_comm8_209 
rij_m_comm8_210 rij_m_comm8_211 rij_m_comm8_212 rij_m_comm8_213 rij_m_comm8_214 rij_m_comm8_215 
rij_m_comm8_216 rij_m_comm8_217 rij_m_comm8_218 rij_m_comm8_219 rij_m_comm8_220 rij_m_comm8_221 
rij_m_comm8_222 rij_m_comm8_223 rij_m_comm8_224 rij_m_comm8_225 rij_m_comm8_226 rij_m_comm8_227 
rij_m_comm8_228 rij_m_comm8_229 rij_m_comm8_230 rij_m_comm8_231 rij_m_comm8_232 rij_m_comm8_233 
rij_m_comm8_234 rij_m_comm8_235 rij_m_comm8_236 rij_m_comm8_237 rij_m_comm8_238 rij_m_comm8_239 
rij_m_comm8_240 rij_m_comm8_241 rij_m_comm8_242 rij_m_comm8_243 rij_m_comm8_244 rij_m_comm8_245 
rij_m_comm8_246 rij_m_comm8_247 rij_m_comm8_248 rij_m_comm8_249 rij_m_comm8_250 rij_m_comm8_251 
rij_m_comm8_252 rij_m_comm8_253 rij_m_comm8_254 rij_m_comm8_255.


Lemma rij_m'_comm8 : forall x y z,
  length x = 8 -> length y = 8 -> length z = 8 ->
    rij_m' 8 x y z = rij_m' 8 y x z.
Proof.
  intros a b c Ha Hb Hc; apply length8 in Ha; apply length8 in Hb; apply length8 in Hc;
  destruct Ha as [a0 H0]; destruct H0 as [a1 H1]; destruct H1 as [a2 H2]; destruct H2 as [a3 H3];
  destruct H3 as [a4 H4]; destruct H4 as [a5 H5]; destruct H5 as [a6 H6]; destruct H6 as [a7 Ha7];
  destruct Hb as [b0 Hb]; destruct Hb as [b1 Hb1]; destruct Hb1 as [b2 Hb2]; destruct Hb2 as [b3 Hb3];
  destruct Hb3 as [b4 Hb4]; destruct Hb4 as [b5 Hb5]; destruct Hb5 as [b6 Hb6]; destruct Hb6 as [b7 Hb7];
  destruct Hc as [c0 Hcc]; destruct Hcc as [c1 Hc1]; destruct Hc1 as [c2 Hc2]; destruct Hc2 as [c3 Hc3];
  destruct Hc3 as [c4 Hc4]; destruct Hc4 as [c5 Hc5]; destruct Hc5 as [c6 Hc6]; destruct Hc6 as [c7 Hc7];
  rewrite Ha7,Hb7,Hc7;
  case c0;case c1;case c2;case c3;case c4;case c5;case c6;case c7.
  apply rij_m'_comm8_255;auto. apply rij_m'_comm8_254;auto. apply rij_m'_comm8_253;auto.
  apply rij_m'_comm8_252;auto. apply rij_m'_comm8_251;auto. apply rij_m'_comm8_250;auto.
  apply rij_m'_comm8_249;auto. apply rij_m'_comm8_248;auto. apply rij_m'_comm8_247;auto.
  apply rij_m'_comm8_246;auto. apply rij_m'_comm8_245;auto. apply rij_m'_comm8_244;auto.
  apply rij_m'_comm8_243;auto. apply rij_m'_comm8_242;auto. apply rij_m'_comm8_241;auto.
  apply rij_m'_comm8_240;auto. apply rij_m'_comm8_239;auto. apply rij_m'_comm8_238;auto.
  apply rij_m'_comm8_237;auto. apply rij_m'_comm8_236;auto. apply rij_m'_comm8_235;auto.
  apply rij_m'_comm8_234;auto. apply rij_m'_comm8_233;auto. apply rij_m'_comm8_232;auto.
  apply rij_m'_comm8_231;auto. apply rij_m'_comm8_230;auto. apply rij_m'_comm8_229;auto.
  apply rij_m'_comm8_228;auto. apply rij_m'_comm8_227;auto. apply rij_m'_comm8_226;auto.
  apply rij_m'_comm8_225;auto. apply rij_m'_comm8_224;auto. apply rij_m'_comm8_223;auto.
  apply rij_m'_comm8_222;auto. apply rij_m'_comm8_221;auto. apply rij_m'_comm8_220;auto.
  apply rij_m'_comm8_219;auto. apply rij_m'_comm8_218;auto. apply rij_m'_comm8_217;auto.
  apply rij_m'_comm8_216;auto. apply rij_m'_comm8_215;auto. apply rij_m'_comm8_214;auto.
  apply rij_m'_comm8_213;auto. apply rij_m'_comm8_212;auto. apply rij_m'_comm8_211;auto.
  apply rij_m'_comm8_210;auto. apply rij_m'_comm8_209;auto. apply rij_m'_comm8_208;auto.
  apply rij_m'_comm8_207;auto. apply rij_m'_comm8_206;auto. apply rij_m'_comm8_205;auto.
  apply rij_m'_comm8_204;auto. apply rij_m'_comm8_203;auto. apply rij_m'_comm8_202;auto.
  apply rij_m'_comm8_201;auto. apply rij_m'_comm8_200;auto. apply rij_m'_comm8_199;auto.
  apply rij_m'_comm8_198;auto. apply rij_m'_comm8_197;auto. apply rij_m'_comm8_196;auto.
  apply rij_m'_comm8_195;auto. apply rij_m'_comm8_194;auto. apply rij_m'_comm8_193;auto.
  apply rij_m'_comm8_192;auto. apply rij_m'_comm8_191;auto. apply rij_m'_comm8_190;auto.
  apply rij_m'_comm8_189;auto. apply rij_m'_comm8_188;auto. apply rij_m'_comm8_187;auto.
  apply rij_m'_comm8_186;auto. apply rij_m'_comm8_185;auto. apply rij_m'_comm8_184;auto.
  apply rij_m'_comm8_183;auto. apply rij_m'_comm8_182;auto. apply rij_m'_comm8_181;auto.
  apply rij_m'_comm8_180;auto. apply rij_m'_comm8_179;auto. apply rij_m'_comm8_178;auto.
  apply rij_m'_comm8_177;auto. apply rij_m'_comm8_176;auto. apply rij_m'_comm8_175;auto.
  apply rij_m'_comm8_174;auto. apply rij_m'_comm8_173;auto. apply rij_m'_comm8_172;auto.
  apply rij_m'_comm8_171;auto. apply rij_m'_comm8_170;auto. apply rij_m'_comm8_169;auto.
  apply rij_m'_comm8_168;auto. apply rij_m'_comm8_167;auto. apply rij_m'_comm8_166;auto.
  apply rij_m'_comm8_165;auto. apply rij_m'_comm8_164;auto. apply rij_m'_comm8_163;auto.
  apply rij_m'_comm8_162;auto. apply rij_m'_comm8_161;auto. apply rij_m'_comm8_160;auto.
  apply rij_m'_comm8_159;auto. apply rij_m'_comm8_158;auto. apply rij_m'_comm8_157;auto.
  apply rij_m'_comm8_156;auto. apply rij_m'_comm8_155;auto. apply rij_m'_comm8_154;auto.
  apply rij_m'_comm8_153;auto. apply rij_m'_comm8_152;auto. apply rij_m'_comm8_151;auto.
  apply rij_m'_comm8_150;auto. apply rij_m'_comm8_149;auto. apply rij_m'_comm8_148;auto.
  apply rij_m'_comm8_147;auto. apply rij_m'_comm8_146;auto. apply rij_m'_comm8_145;auto.
  apply rij_m'_comm8_144;auto. apply rij_m'_comm8_143;auto. apply rij_m'_comm8_142;auto.
  apply rij_m'_comm8_141;auto. apply rij_m'_comm8_140;auto. apply rij_m'_comm8_139;auto.
  apply rij_m'_comm8_138;auto. apply rij_m'_comm8_137;auto. apply rij_m'_comm8_136;auto.
  apply rij_m'_comm8_135;auto. apply rij_m'_comm8_134;auto. apply rij_m'_comm8_133;auto.
  apply rij_m'_comm8_132;auto. apply rij_m'_comm8_131;auto. apply rij_m'_comm8_130;auto.
  apply rij_m'_comm8_129;auto. apply rij_m'_comm8_128;auto. apply rij_m'_comm8_127;auto.
  apply rij_m'_comm8_126;auto. apply rij_m'_comm8_125;auto. apply rij_m'_comm8_124;auto.
  apply rij_m'_comm8_123;auto. apply rij_m'_comm8_122;auto. apply rij_m'_comm8_121;auto.
  apply rij_m'_comm8_120;auto. apply rij_m'_comm8_119;auto. apply rij_m'_comm8_118;auto.
  apply rij_m'_comm8_117;auto. apply rij_m'_comm8_116;auto. apply rij_m'_comm8_115;auto.
  apply rij_m'_comm8_114;auto. apply rij_m'_comm8_113;auto. apply rij_m'_comm8_112;auto.
  apply rij_m'_comm8_111;auto. apply rij_m'_comm8_110;auto. apply rij_m'_comm8_109;auto.
  apply rij_m'_comm8_108;auto. apply rij_m'_comm8_107;auto. apply rij_m'_comm8_106;auto.
  apply rij_m'_comm8_105;auto. apply rij_m'_comm8_104;auto. apply rij_m'_comm8_103;auto.
  apply rij_m'_comm8_102;auto. apply rij_m'_comm8_101;auto. apply rij_m'_comm8_100;auto.
  apply rij_m'_comm8_99;auto. apply rij_m'_comm8_98;auto. apply rij_m'_comm8_97;auto.
  apply rij_m'_comm8_96;auto. apply rij_m'_comm8_95;auto. apply rij_m'_comm8_94;auto.
  apply rij_m'_comm8_93;auto. apply rij_m'_comm8_92;auto. apply rij_m'_comm8_91;auto.
  apply rij_m'_comm8_90;auto. apply rij_m'_comm8_89;auto. apply rij_m'_comm8_88;auto.
  apply rij_m'_comm8_87;auto. apply rij_m'_comm8_86;auto. apply rij_m'_comm8_85;auto.
  apply rij_m'_comm8_84;auto. apply rij_m'_comm8_83;auto. apply rij_m'_comm8_82;auto.
  apply rij_m'_comm8_81;auto. apply rij_m'_comm8_80;auto. apply rij_m'_comm8_79;auto.
  apply rij_m'_comm8_78;auto. apply rij_m'_comm8_77;auto. apply rij_m'_comm8_76;auto.
  apply rij_m'_comm8_75;auto. apply rij_m'_comm8_74;auto. apply rij_m'_comm8_73;auto.
  apply rij_m'_comm8_72;auto. apply rij_m'_comm8_71;auto. apply rij_m'_comm8_70;auto.
  apply rij_m'_comm8_69;auto. apply rij_m'_comm8_68;auto. apply rij_m'_comm8_67;auto.
  apply rij_m'_comm8_66;auto. apply rij_m'_comm8_65;auto. apply rij_m'_comm8_64;auto.
  apply rij_m'_comm8_63;auto. apply rij_m'_comm8_62;auto. apply rij_m'_comm8_61;auto.
  apply rij_m'_comm8_60;auto. apply rij_m'_comm8_59;auto. apply rij_m'_comm8_58;auto.
  apply rij_m'_comm8_57;auto. apply rij_m'_comm8_56;auto. apply rij_m'_comm8_55;auto.
  apply rij_m'_comm8_54;auto. apply rij_m'_comm8_53;auto. apply rij_m'_comm8_52;auto.
  apply rij_m'_comm8_51;auto. apply rij_m'_comm8_50;auto. apply rij_m'_comm8_49;auto.
  apply rij_m'_comm8_48;auto. apply rij_m'_comm8_47;auto. apply rij_m'_comm8_46;auto.
  apply rij_m'_comm8_45;auto. apply rij_m'_comm8_44;auto. apply rij_m'_comm8_43;auto.
  apply rij_m'_comm8_42;auto. apply rij_m'_comm8_41;auto. apply rij_m'_comm8_40;auto.
  apply rij_m'_comm8_39;auto. apply rij_m'_comm8_38;auto. apply rij_m'_comm8_37;auto.
  apply rij_m'_comm8_36;auto. apply rij_m'_comm8_35;auto. apply rij_m'_comm8_34;auto.
  apply rij_m'_comm8_33;auto. apply rij_m'_comm8_32;auto. apply rij_m'_comm8_31;auto.
  apply rij_m'_comm8_30;auto. apply rij_m'_comm8_29;auto. apply rij_m'_comm8_28;auto.
  apply rij_m'_comm8_27;auto. apply rij_m'_comm8_26;auto. apply rij_m'_comm8_25;auto.
  apply rij_m'_comm8_24;auto. apply rij_m'_comm8_23;auto. apply rij_m'_comm8_22;auto.
  apply rij_m'_comm8_21;auto. apply rij_m'_comm8_20;auto. apply rij_m'_comm8_19;auto.
  apply rij_m'_comm8_18;auto. apply rij_m'_comm8_17;auto. apply rij_m'_comm8_16;auto.
  apply rij_m'_comm8_15;auto. apply rij_m'_comm8_14;auto. apply rij_m'_comm8_13;auto.
  apply rij_m'_comm8_12;auto. apply rij_m'_comm8_11;auto. apply rij_m'_comm8_10;auto.
  apply rij_m'_comm8_9;auto.  apply rij_m'_comm8_8;auto.  apply rij_m'_comm8_7;auto.
  apply rij_m'_comm8_6;auto.  apply rij_m'_comm8_5;auto.  apply rij_m'_comm8_4;auto.
  apply rij_m'_comm8_3;auto.  apply rij_m'_comm8_2;auto.  apply rij_m'_comm8_1;auto.
  apply rij_m'_comm8_0;auto.
Qed.



























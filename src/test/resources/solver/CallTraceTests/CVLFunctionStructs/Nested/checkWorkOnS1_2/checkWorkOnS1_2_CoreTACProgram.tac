TACSymbolTable {
	UserDefined {
		UninterpSort skey
	}
	BuiltinFunctions {
		to_skey:JSON{"#class":"vc.data.TACBuiltInFunction.Hash.ToSkey"}
		skey_basic:JSON{"#class":"vc.data.TACBuiltInFunction.Hash.Basic"}
		safe_math_narrow_bv256:JSON{"#class":"vc.data.TACBuiltInFunction.SafeMathNarrow","returnSort":{"bits":256}}
		hash_3_keccak:JSON{"#class":"vc.data.TACBuiltInFunction.Hash.SimpleHashApplication","arity":3,"hashFamily":{"#class":"vc.data.HashFamily.Keccack"}}
		skey_add:JSON{"#class":"vc.data.TACBuiltInFunction.Hash.Addition"}
	}
	UninterpretedFunctions {
	}
	tacMCANON0havocme2376!!5:bytemap:0
	tacMCANON0!!55:bytemap:1
	tacMCANON0!!57:bytemap:1
	tacMCANON0!!61:bytemap:1
	tacMCANON0!!68:bytemap:1
	tacMCANON0!!70:bytemap:1
	tacMCANON0!!72:bytemap:1
	tacMCANON0!!76:bytemap:1
	tacMCANON0!!80:bytemap:1
	tacMCANON0!!86:bytemap:1
	tacMCANON0!!91:bytemap:1
	tacMCANON0!!98:bytemap:1
	tacM0x40@1:bv256:2
	tacCodesizeCANON0:bv256:3
	tacCalldatabufCANON0@1:bv256:4
	tacMCANON1!!6:bytemap:5
	CANON38!!11:wordmap:6
	CANON39!!12:wordmap:7
	tacM0x40!!0:bv256:2
	tacAddress!!42:bv256:8
	lastReverted:bool:9
	CANON2!!30:int:10
	tacExtcodesize!!4:wordmap:11
	CANON35!!9:wordmap:12
	CANON40!!13:wordmap:13
	CANON41!!14:wordmap:14
	tacCalldatasize:bv256:15
	tacCalldatasize@1:bv256:15
	tacReturndata@1:bytemap:16
	calledContract:int:17
	CANON41!!144:wordmap:14
	CANON46!!15:wordmap:18
	CANON48!!16:wordmap:19
	tacExtcodesize:wordmap:11
	CANON100@2:bv256:20
	CANON101@2:bv256:21
	CANON102:bool:22
	CANON103:int:23
	CANON104:int:24
	CANON105:bool:22
	CANON106:bool:25
	CANON107:int:26
	CANON108@2:bv256:21
	CANON109@2:bv256:27
	CANON110@2:bool:21
	CANON111@2:bv256:21
	CANON112:bool:22
	CANON113:int:26
	CANON114@2:bv256:21
	CANON115@2:bv256:28
	CANON116@2:bv256:21
	CANON117:bool:22
	CANON118:int:23
	CANON119:int:29
	CANON120:bool:22
	CANON121:bool:25
	CANON122:bool
	CANON123:int:26
	CANON124:bv256:21
	CANON125:bv256:30
	CANON126:bv256:21
	CANON127:bool:21
	CANON128:bool:22
	tacCalldatasize!!39:bv256:15
	tacMCANON0havocme2376@1:bytemap:0
	tacMCANON0@1:bytemap:1
	tacMCANON1@1:bytemap:5
	tacMCANON2@1:bytemap:31
	tacBalance:wordmap:32
	CANON50!!17:wordmap:33
	tacBalance!!47:wordmap:32
	CANON52!!18:wordmap:34
	CANON53!!19:wordmap:35
	CANON54!!20:wordmap:36
	tacBalance!!7:wordmap:32
	CANON55!!21:wordmap:37
	lastReverted!!2:bool:9
	tacCalldatabuf@1:bytemap:38
	R1:bv256:3
	B32:bool:21
	B33:bool:21
	B36:bool:22
	B73:bool:39
	B83:bool:39
	I34:int:23
	I35:int:24
	I37:int:40
	I38:int:23
	I46:int:21
	I49:int:21
	R10:bv256:21
	R25:bv256:41
	R26:bv256:42
	R27:bv256:43
	R28:bv256:44
	R31:bv256:21
	R40:bv256:21
	R43:bv256:21
	R44:bv256:21
	R45:bv256:21
	R48:bv256:21
	R50:bv256:21
	R51:bv256:21
	R52:bv256:45
	R53:(uninterp) skey:46
	R54:bv256:21
	R56:bv256:47
	R58:bv256:48
	R59:bv256:48
	R60:bv256:49
	R62:(uninterp) skey:48
	R63:bv256:48
	R64:bv256:48
	R65:bv256:48
	R66:bv256:48
	R67:bv256:50
	R69:bv256:51
	R71:bv256:52
	R74:bv256:39
	R75:bv256:53
	R77:(uninterp) skey:48
	R78:bv256:48
	R79:bv256:54
	R81:(uninterp) skey:48
	R82:bv256:48
	R84:bv256:39
	R85:bv256:55
	R87:(uninterp) skey:56
	R88:bv256:48
	R89:bv256:48
	R90:bv256:57
	R92:(uninterp) skey:48
	R93:bv256:48
	R94:bv256:48
	R95:bv256:48
	R96:bv256:48
	R97:bv256:58
	R99:bv256:59
	B103:bool:39
	B113:bool:39
	B119:bool:60
	B129:bool:21
	B130:bool:21
	B131:bool:21
	B132:bool:21
	B133:bool:21
	B134:bool:21
	B135:bool:21
	B136:bool:21
	B137:bool:21
	B138:bool:21
	B142:bool:21
	B145:bool:22
	B150:bool:22
	B153:bool:22
	B157:bool:21
	B160:bool:22
	B165:bool:22
	B168:bool:22
	B175:bool:21
	B176:bool:22
	I139:int:26
	I146:int:26
	I151:int:23
	I152:int:24
	I154:int:26
	I161:int:26
	I166:int:23
	I167:int:29
	I171:int:26
	R101:bv256:61
	R104:bv256:39
	R105:bv256:62
	R107:(uninterp) skey:48
	R108:bv256:48
	R109:bv256:63
	R111:(uninterp) skey:48
	R112:bv256:48
	R114:bv256:39
	R115:bv256:64
	R117:(uninterp) skey:56
	R118:bv256:56
	R120:bv256:60
	R121:bv256:65
	R123:bv256:66
	R124:bv256:67
	R125:bv256:68
	R126:bv256:68
	R140:(uninterp) skey:21
	R141:(uninterp) skey:21
	R143:bv256:21
	R147:(uninterp) skey:21
	R148:(uninterp) skey:21
	R149:bv256:21
	R155:(uninterp) skey:21
	R156:(uninterp) skey:21
	R158:bv256:21
	R162:(uninterp) skey:21
	R163:(uninterp) skey:21
	R164:bv256:21
	R172:(uninterp) skey:21
	R173:(uninterp) skey:21
	R174:bv256:21
	lastHasThrown!!169:bool:69
	CANON22!8:ghostmap(bv256*bv256*bv256->bv256):70
	tacAddress@1:bv256:8
	lastReverted!!170:bool:9
	LCANON0@1:bv256:45
	LCANON1@1:bv256:46
	LCANON2@1:bv256:71
	LCANON3@1:bv256:48
	LCANON4@1:bv256:72
	LCANON5@1:bv256:48
	LCANON6@1:bv256:48
	LCANON7@1:bv256:48
	LCANON8@1:bv256:48
	LCANON9@1:bool:39
	CANON60!!22:wordmap:73
	tacMCANON0!!100:bytemap:1
	tacMCANON0!!102:bytemap:1
	tacMCANON0!!106:bytemap:1
	tacMCANON0!!110:bytemap:1
	tacMCANON0!!116:bytemap:1
	tacMCANON0!!122:bytemap:1
	CANON62!!23:wordmap:74
	CANON10:int:75
	CANON11:int:76
	CANON12:int:77
	CANON13:int:78
	CANON14:int:79
	CANON15:int:80
	CANON16:int:81
	CANON17:int:82
	CANON18:int:83
	CANON19:int:40
	CANON20:int:23
	CANON22:ghostmap(bv256*bv256*bv256->bv256):70
	CANON23:bv256:21
	CANON24:bv256:21
	CANON25:bv256:21
	CANON26:bv256:21
	CANON27:bv256:21
	CANON28:int:21
	CANON29:bv256:21
	CANON30:int:21
	CANON31:bv256:21
	CANON32@1:bv256:21
	CANON33@1:bv256:21
	CANON34@1:bv256:47
	CANON35:wordmap:12
	CANON36@1:bv256:21
	CANON37@1:bv256:49
	CANON38:wordmap:6
	CANON39:wordmap:7
	CANON40:wordmap:13
	CANON41:wordmap:14
	CANON42@1:bv256:50
	CANON43@1:bv256:51
	CANON44@1:bv256:52
	CANON45@1:bv256:53
	CANON46:wordmap:18
	CANON47@1:bv256:54
	CANON48:wordmap:19
	CANON49@1:bv256:55
	CANON50:wordmap:33
	CANON51@1:bv256:57
	CANON52:wordmap:34
	CANON53:wordmap:35
	CANON54:wordmap:36
	CANON55:wordmap:37
	CANON56@1:bv256:58
	CANON57@1:bv256:59
	CANON58@1:bv256:61
	CANON59@1:bv256:62
	CANON60:wordmap:73
	CANON61@1:bv256:63
	CANON62:wordmap:74
	CANON63@1:bv256:64
	CANON64:wordmap:84
	CANON65@1:bv256:65
	CANON66:int:85
	CANON67:bool:21
	CANON68:bool:21
	CANON69:bool:21
	CANON70:bool:21
	CANON71:bool:21
	CANON72:bool:21
	CANON73:bool:21
	CANON74:bool:21
	CANON75:bool:21
	CANON76:bool:21
	CANON77:int:86
	CANON78:int:87
	CANON79:int:88
	CANON80:int:89
	CANON81:bool:90
	CANON82:int:91
	CANON83:bool:92
	CANON84:int:93
	CANON85:int:94
	CANON86:int:95
	CANON87:int:96
	CANON88:bool:97
	CANON89:int:98
	CANON90:bool:99
	CANON91:bool:100
	CANON92:int:26
	CANON93@2:bv256:21
	CANON94@2:bv256:101
	CANON95@2:bool:21
	CANON96@2:bv256:21
	CANON97:bool:22
	CANON98:int:26
	CANON99@2:bv256:21
	CANON64!!24:wordmap:84
	LCANON10@1:bv256:39
	LCANON11@1:bv256:102
	LCANON12@1:bv256:48
	LCANON13@1:bv256:103
	LCANON14@1:bv256:48
	LCANON15@1:bool:39
	LCANON16@1:bv256:39
	LCANON17@1:bv256:56
	LCANON18@1:bv256:104
	LCANON19@1:bv256:48
	LCANON20@1:bv256:105
	LCANON21@1:bv256:48
	LCANON22@1:bv256:48
	LCANON23@1:bv256:48
	LCANON24@1:bv256:48
	LCANON25@1:bool:39
	LCANON26@1:bv256:39
	LCANON27@1:bv256:106
	LCANON28@1:bv256:48
	LCANON29@1:bv256:107
	LCANON30@1:bv256:48
	LCANON31@1:bool:39
	LCANON32@1:bv256:39
	LCANON33@1:bv256:108
	LCANON34@1:bv256:56
	LCANON35@1:bool:60
	LCANON36@1:bv256:60
	LCANON37@1:bv256:66
	LCANON38@1:bv256:67
	LCANON39@1:bv256:68
	LCANON40@1:bv256:68
	CANON64!!159:wordmap:84
	tacContractAtCANON1:bv256:41
	tacContractAtCANON2:bv256:42
	tacContractAtCANON3:bv256:43
	executingContract:int:109
	lastHasThrown:bool:69
	CANON2!!128:int:10
	tacReturndata!!127:bytemap:16
	CANON1:int:110
	CANON2:int:10
	CANON3:bv256:21
	CANON4:bool:21
	CANON5:bool:21
	CANON6:int:23
	CANON7:int:24
	CANON8:bool:22
	CANON9:int:111
	tacContractAtCANON:bv256:44
	tacCalldatasize!!3:bv256:15
	lastHasThrown!!41:bool:69
	tacSighash!!29:bv256:112
	tacSighash@1:bv256:112
	CANON:int:113
}
Program {
	Block 0_0_0_0_0_0 Succ [1_0_0_1_0_0] {
		AssignHavocCmd tacM0x40!!0:2
		AssumeExpCmd Le(tacM0x40!!0:2 0x80 )
		AssignHavocCmd R1:3
		AssumeExpCmd Ge(R1:3 0x1 )
		AssignHavocCmd lastReverted!!2:9
		AssignHavocCmd tacCalldatasize!!3:15
		AssignHavocCmd tacExtcodesize!!4:11
		AssignExpCmd tacMCANON0havocme2376!!5:0 MapDefinition(i.2386:bv256 -> 0x0 bytemap)
		AssignExpCmd tacMCANON1!!6:5 MapDefinition(i.2387:bv256 -> 0x0 bytemap)
		AssignHavocCmd tacBalance!!7:32
		AssignHavocCmd CANON10:75
		AssumeExpCmd Eq(CANON10:75 0x0(int) )
		AssignHavocCmd CANON11:76
		AssumeExpCmd LAnd(Ge(CANON11:76 0x0(int) ) Le(CANON11:76 0xffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON12:77
		AssumeExpCmd LAnd(Ge(CANON12:77 0x0(int) ) Le(CANON12:77 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON13:78
		AssumeExpCmd LAnd(Ge(CANON13:78 0x0(int) ) Le(CANON13:78 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON14:79
		AssumeExpCmd LAnd(Ge(CANON14:79 0x0(int) ) Le(CANON14:79 0xffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON15:80
		AssumeExpCmd LAnd(Ge(CANON15:80 0x0(int) ) Le(CANON15:80 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON16:81
		AssumeExpCmd LAnd(Ge(CANON16:81 0x0(int) ) Le(CANON16:81 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON17:82
		AssumeExpCmd LAnd(Ge(CANON17:82 0x0(int) ) Le(CANON17:82 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON18:83
		AssumeExpCmd LAnd(Ge(CANON18:83 0x0(int) ) Le(CANON18:83 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd CANON22!8:70
		AssignHavocCmd CANON35!!9:12
		AssignHavocCmd R10:21
		AssignHavocCmd CANON38!!11:6
		AssignHavocCmd CANON39!!12:7
		AssignHavocCmd CANON40!!13:13
		AssignHavocCmd CANON41!!14:14
		AssignHavocCmd CANON46!!15:18
		AssignHavocCmd CANON48!!16:19
		AssignHavocCmd CANON50!!17:33
		AssignHavocCmd CANON52!!18:34
		AssignHavocCmd CANON53!!19:35
		AssignHavocCmd CANON54!!20:36
		AssignHavocCmd CANON55!!21:37
		AssignHavocCmd CANON60!!22:73
		AssignHavocCmd CANON62!!23:74
		AssignHavocCmd CANON64!!24:84
		AssignHavocCmd R25:41
		AssumeExpCmd Eq(R25:41 0x1 )
		AssignHavocCmd R26:42
		AssumeExpCmd Eq(R26:42 0x2 )
		AssignHavocCmd R27:43
		AssumeExpCmd Eq(R27:43 0x4 )
		AssignHavocCmd CANON9:111
		AssumeExpCmd LAnd(Ge(CANON9:111 0x0(int) ) Le(CANON9:111 0xffffffffffffffffffffffffffffffffffffffff(int) ) )
		AssignHavocCmd R28:44
		AssumeExpCmd LAnd(Ge(R28:44 0x1 ) Le(R28:44 0xffffffffffffffffffffffffffffffffffffffff ) )
		AssignHavocCmd tacSighash!!29:112
		AssumeExpCmd Eq(tacSighash!!29:112 0x4166f100 )
		AnnotationCmd JSON{"key":{"name":"tac.state.extension","type":"analysis.icfg.Inliner$ExtendedStateVars","erasureStrategy":"Canonical"},"value":"rO0ABXNyACdhbmFseXNpcy5pY2ZnLklubGluZXIkRXh0ZW5kZWRTdGF0ZVZhcnOvh/MjxNFkQAIAAUwAFmluc3RhbmNlVG9FeHRlbmRlZFZhcnN0AA9MamF2YS91dGlsL01hcDt4cHNyACFkYXRhc3RydWN0dXJlcy5MaW5rZWRBcnJheUhhc2hNYXAAAAAAAAAAAQMAAkYACmxvYWRGYWN0b3JMAAloYXNoVGFibGV0AC5MZGF0YXN0cnVjdHVyZXMvYXJyYXloYXNodGFibGUvQXJyYXlIYXNoVGFibGU7eHB3CAAAAAFAAAAAc3IAFGphdmEubWF0aC5CaWdJbnRlZ2VyjPyfH6k7+x0DAAZJAAhiaXRDb3VudEkACWJpdExlbmd0aEkAE2ZpcnN0Tm9uemVyb0J5dGVOdW1JAAxsb3dlc3RTZXRCaXRJAAZzaWdudW1bAAltYWduaXR1ZGV0AAJbQnhyABBqYXZhLmxhbmcuTnVtYmVyhqyVHQuU4IsCAAB4cP///////////////v////4AAAABdXIAAltCrPMX+AYIVOACAAB4cAAAABDORgSgAAAAAAAAAAAAAAABeHNxAH4AA3cIAAAAAEAAAAB4eA=="}
		AnnotationCmd:114 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"rule parameters setup"}}
		AssignHavocCmd CANON:113
		AssumeExpCmd LAnd(Ge(CANON:113 0x0(int) ) Le(CANON:113 0x2(int) ) )
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLArg.PrimitiveArg","callIndex":0,"index":0,"sym":{"namePrefix":"CANON","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":27,"charByteOffset":21},"end":{"line":27,"charByteOffset":27}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"x"}]},"param":{"Named_type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"id":"x","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":27,"charByteOffset":21},"end":{"line":27,"charByteOffset":27}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.trace.declaration","type":"spec.CVLCompiler$Companion$TraceMeta$VariableDeclaration","erasureStrategy":"Erased"},"value":{"v":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar","t":{"namePrefix":"CANON","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":27,"charByteOffset":21},"end":{"line":27,"charByteOffset":27}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"x"}]}},"t":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"type":{"#class":"spec.CVLCompiler.Companion.TraceMeta.DeclarationType.Parameter","sourceName":"x"},"fields":null}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":0}
		AnnotationCmd:115 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"Setup"}}
		AnnotationCmd:116 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"multi contract setup"}}
		AssignExpCmd CANON1:110 R28:117
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":2}
		AnnotationCmd:118 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"contract address vars initialized"}}
		AssignExpCmd CANON2!!30:10 R28:117
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":3}
		AnnotationCmd:119 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"setup read tracking instrumentation"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":4}
		AnnotationCmd:120 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"last storage initialize"}}
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet.StorageTakeSnapshot","lhs":{"namePrefix":"lastStorage","tag":{"#class":"tac.Tag.BlockchainState"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule"}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"lastStorage"}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"lastStorage"}]}}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":5}
		AnnotationCmd:121 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assuming contracts in scene with non-empty bytecode have EXTCODESIZE larger than zero"}}
		AssignExpCmd R31:21 Select(tacExtcodesize!!4:11 Apply(to_skey:bif R28:117) )
		AssumeExpCmd Ge(R31:21 0x1 )
		AssumeExpCmd Eq(R31:122 R1:123 )
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":6}
		AnnotationCmd:124 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assuming address(0).code has no code deployed"}}
		AssignExpCmd B33:21 Eq(Select(tacExtcodesize!!4:11 Apply(skey_basic:bif 0x0) ) 0x0 )
		AssumeCmd B33:21 "expToAssumeCmd"
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":7}
		AnnotationCmd:125 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assumptions about contracts' addresses"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":8}
		AnnotationCmd:126 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assumptions about static addresses"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":9}
		AnnotationCmd:127 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"establish addresses of precompiled contracts"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":10}
		AnnotationCmd:128 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"assumptions about uniqueness of contracts' addresses"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":11}
		AnnotationCmd:129 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"static links"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":12}
		AnnotationCmd:130 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"record starting nonces"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":13}
		AnnotationCmd:131 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"cloned contracts have no balances"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":14}
		AnnotationCmd:132 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"Linked immutable setup"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":15}
		AnnotationCmd:133 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"Constrain immutables"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":16}
		AnnotationCmd:134 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Message","s":"establish equivalence of extension and base contract immutables"}}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":17}
		AnnotationCmd JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1}
		AnnotationCmd:135 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.AssumeCmd.Assume","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":28,"charByteOffset":4},"end":{"line":28,"charByteOffset":18}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.ArithRelopExp.LtExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"x","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":28,"charByteOffset":12},"end":{"line":28,"charByteOffset":13}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"3","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"3"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":28,"charByteOffset":16},"end":{"line":28,"charByteOffset":17}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":28,"charByteOffset":12},"end":{"line":28,"charByteOffset":17}}}},"description":null,"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"comesFromSpec":true}}}
		AssignExpCmd:136 I34:23 CANON:113
		AssignExpCmd:137 I35:24 0x3
		AssignExpCmd:138 B36:22 true
		AnnotationCmd:139 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":18}
		AnnotationCmd:140 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Declaration","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}},"cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"id":"e","scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.trace.declaration","type":"spec.CVLCompiler$Companion$TraceMeta$VariableDeclaration","erasureStrategy":"Erased"},"value":{"v":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.CVLVar","id":"e878"},"t":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"type":{"#class":"spec.CVLCompiler.Companion.TraceMeta.DeclarationType.Variable"},"fields":[[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"coinbase"}],{"namePrefix":"CANON14","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.coinbase"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"basefee"}],{"namePrefix":"CANON12","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.basefee"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"timestamp"}],{"namePrefix":"CANON18","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.timestamp"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"blobbasefee"}],{"namePrefix":"CANON13","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.blobbasefee"}]},[{"#class":"tac.DataField.StructField","field":"tx"},{"#class":"tac.DataField.StructField","field":"origin"}],{"namePrefix":"CANON11","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.tx.origin"}]},[{"#class":"tac.DataField.StructField","field":"msg"},{"#class":"tac.DataField.StructField","field":"sender"}],{"namePrefix":"CANON9","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.msg.sender"}]},[{"#class":"tac.DataField.StructField","field":"msg"},{"#class":"tac.DataField.StructField","field":"value"}],{"namePrefix":"CANON10","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.msg.value"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"difficulty"}],{"namePrefix":"CANON15","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.difficulty"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"gaslimit"}],{"namePrefix":"CANON16","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.gaslimit"}]},[{"#class":"tac.DataField.StructField","field":"block"},{"#class":"tac.DataField.StructField","field":"number"}],{"namePrefix":"CANON17","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"fields":[{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":30,"charByteOffset":4},"end":{"line":30,"charByteOffset":10}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"e.block.number"}]}]}}
		AnnotationCmd:141 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":19}
		AnnotationCmd:142 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Apply","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":31,"charByteOffset":4},"end":{"line":31,"charByteOffset":22}},"exp":{"#class":"spec.cvlast.CVLExp.ApplyExp.ContractFunction.Concrete","methodIdWithCallContext":{"#class":"spec.cvlast.ConcreteMethod","signature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"workOnS1Ext"},"params":[{"#class":"spec.cvlast.VMParam.Named","name":"x","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"utils.Range.Empty"}}],"res":[]},"sighashInt":{"n":"4166f100"}}},"args":[{"#class":"spec.cvlast.CVLExp.VariableExp","id":"e","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"env","fields":[{"fieldName":"msg","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"msg","fields":[{"fieldName":"sender","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"value","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"fieldName":"tx","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"tx","fields":[{"fieldName":"origin","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"fieldName":"block","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"block","fields":[{"fieldName":"basefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"blobbasefee","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"coinbase","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"difficulty","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"gaslimit","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"number","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"timestamp","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}}]},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":31,"charByteOffset":16},"end":{"line":31,"charByteOffset":17}}},"twoStateIndex":"NEITHER"},{"#class":"spec.cvlast.CVLExp.VariableExp","id":"x","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":31,"charByteOffset":19},"end":{"line":31,"charByteOffset":20}}},"twoStateIndex":"NEITHER"}],"noRevert":true,"storage":{"id":"lastStorage","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"},"range":{"#class":"utils.Range.Empty","comment":"empty storage type"}},"twoStateIndex":"NEITHER"},"isWhole":false,"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Void"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":31,"charByteOffset":4},"end":{"line":31,"charByteOffset":21}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CallResolution$DirectPassing","target":{"methodSignature":{"#class":"spec.cvlast.ExternalQualifiedMethodSignature.ExternalQualifiedMethodSig","wrapped":{"#class":"spec.cvlast.QualifiedMethodSignature.QualifiedMethodSig","qualifiedMethodName":{"#class":"spec.cvlast.QualifiedFunction","host":{"name":"TestContract"},"methodId":"workOnS1Ext"},"params":[{"#class":"spec.cvlast.VMParam.Named","name":"x","vmType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"range":{"#class":"utils.Range.Empty"}}],"res":[]},"sighashInt":{"n":"4166f100"}},"definitelyNonPayable":true,"annotation":{"visibility":"EXTERNAL","envFree":false,"library":false,"virtual":false},"stateMutability":"nonpayable","evmExternalMethodInfo":{"sigHash":"4166f100","name":"workOnS1Ext","argTypes":[{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}],"resultTypes":[],"stateMutability":"nonpayable","isConstant":false,"paramNames":["x"],"isLibrary":false,"contractName":"TestContract","contractInstanceId":"ce4604a0000000000000000000000001","sourceSegment":{"range":{"specFile":"TestContract.sol","start":{"line":21,"charByteOffset":4},"end":{"line":23,"charByteOffset":5}},"content":"function workOnS1Ext(uint x) external {\n        this.workOnS1(x, m[0]);\n    }"}}},"hasEnv":true}}},"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AnnotationCmd JSON{"key":{"name":"cvl.trace.data.movement","type":"spec.CVLCompiler$Companion$TraceMeta$CVLMovement","erasureStrategy":"Erased"},"value":{"dst":{"id":"certoraArg888890"},"src":{"id":"e878"}}}
		AssignExpCmd:143 I38:23 CANON:113
	}
	Block 1_0_0_1_0_0 Succ [2_0_0_2_0_1] {
		AnnotationCmd:144 JSON{"key":{"name":"call.trace.push","type":"analysis.icfg.Inliner$CallStack$PushRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"4166f100"},"attr":{"#class":"scene.MethodAttribute.Common"}},"summary":null,"convention":{"#class":"analysis.icfg.Inliner.CallConventionType.FromCVL"},"calleeId":1}}
		AssignHavocCmd:144 tacCalldatasize!!39:15
		AssumeExpCmd Eq(tacCalldatasize!!39:15 0x24 )
		AssignExpCmd:144 tacCalldatabuf@1:38 MapDefinition(CANON21.2383:bv256 -> Ite(Lt(CANON21.2383 tacCalldatasize!!39:15 ) Select(Select(Select(CANON22!8:70 CANON21.2383 ) tacCalldatasize!!39:15 ) 0x4166f100 ) 0x0 ) bytemap)
		AssignExpCmd:144 R40:21 Select(Select(Select(CANON22!8:70 0x0 ) 0x24 ) 0x4166f100 )
		AssumeExpCmd LAnd(Ge(R40:21 0x4166f10000000000000000000000000000000000000000000000000000000000 ) Le(R40:21 0x4166f100ffffffffffffffffffffffffffffffffffffffffffffffffffffffff ) )
		AnnotationCmd:144 JSON{"key":{"name":"cvl.arg-serialization.start","type":"spec.CVLInvocationCompiler$StartSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":0,"callId":1}}
		LabelCmd:144 "0: Read primitive from certoraArg891892:int..."
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int elements of a user array)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int elements of a user array)"
		AssignExpCmd:144 tacCalldatabufCANON0@1:145 Apply(safe_math_narrow_bv256:bif I38:23)
		LabelCmd:144 "...done 0"
		AnnotationCmd JSON{"key":{"name":"cvl.trace.external","type":"spec.CVLCompiler$Companion$TraceMeta$ExternalArg","erasureStrategy":"Erased"},"value":{"s":{"#class":"spec.CVLCompiler.Companion.TraceMeta.ValueIdentity.TACVar","t":{"namePrefix":"I38","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},"rootOffset":"0","callId":1,"targetType":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"sourceType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"fields":null}}
		AnnotationCmd:144 JSON{"key":{"name":"cvl.arg-serialization.end","type":"spec.CVLInvocationCompiler$EndSerializationMarker","erasureStrategy":"Canonical"},"value":{"id":0,"callId":1}}
		AssignExpCmd:144 lastHasThrown!!41:69 false
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssertCmd:144 true "sanity bounds check on cvl to vm encoding failed (unsigned int)"
		AssignExpCmd:144 R43:21 Apply(safe_math_narrow_bv256:bif CANON9:111)
		AssignExpCmd:144 R45:21 Select(tacBalance!!7:32 Apply(to_skey:bif R43:21) )
		AssignExpCmd:146 tacBalance!!47:32 Store(tacBalance!!7:32 Apply(to_skey:bif R43:21) R45:21 )
		AssignExpCmd:144 R48:21 Select(tacBalance!!47:32 Apply(to_skey:bif R28:117) )
		AssignExpCmd:146 R50:21 Apply(safe_math_narrow_bv256:bif R48:21)
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.TransferSnippet","srcAccountInfo":{"old":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R45","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"new":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R45","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"addr":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R43","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]}},"trgAccountInfo":{"old":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R48","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"new":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R50","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"addr":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R28","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"tacContractAt"}},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"}]}},"transferredAmount":{"#class":"vc.data.TACSymbol.Const","value":"0"}}}
		LabelCmd:144 "Start procedure TestContract-workOnS1Ext(uint256)"
		AnnotationCmd:144 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AssignExpCmd:144 R51:21 Select(tacExtcodesize!!4:11 Apply(to_skey:bif R28:147) )
		AssumeExpCmd Ge(R51:21 0x1 )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.RawStorageAccess.WithLocSym","isLoad":true,"loc":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R28","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"tacAddress","maybeTACKeywordOrdinal":22}},{"key":{"name":"tac.env.known-bit-width","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":160},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"}]},"contractInstance":"ce4604a0000000000000000000000001","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R51","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"storageType":null,"range":null}}
		AnnotationCmd:144 JSON{"key":{"name":"internal.func.finder.info","type":"analysis.ip.InternalFunctionFinderReport","erasureStrategy":"Erased"},"value":{"unresolvedFunctions":[]}}
		AnnotationCmd:144 JSON{"key":{"name":"fps.free-pointer-is-scalarized","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":0,"bytecodeCount":8,"sources":[{"source":0,"begin":25,"end":1954}]}}
		LabelCmd "→ Assuming FP is strictly monotonic increasing"
		LabelCmd "←"
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":0,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":2,"charByteOffset":0},"end":{"line":43,"charByteOffset":1}},"content":"contract TestContract {...}"}}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":0}}
		AnnotationCmd:148 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":16,"bytecodeCount":7,"sources":[{"source":0,"begin":25,"end":1954}]}}
		AnnotationCmd:148 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":26,"bytecodeCount":9,"sources":[{"source":0,"begin":25,"end":1954}]}}
		AnnotationCmd:148 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":81,"bytecodeCount":14,"sources":[{"source":0,"begin":319,"end":396}]}}
		AnnotationCmd:149 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1066,"bytecodeCount":10,"sources":[{"source":1,"begin":690,"end":1019},{"source":1,"begin":749,"end":755},{"source":1,"begin":798,"end":800},{"source":1,"begin":786,"end":795},{"source":1,"begin":777,"end":784},{"source":1,"begin":773,"end":796},{"source":1,"begin":769,"end":801},{"source":1,"begin":766,"end":885}]}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":1,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":21,"charByteOffset":4},"end":{"line":23,"charByteOffset":5}},"content":"compiler-generate condition in function workOnS1Ext(uint x) external "}}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":1}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1088,"bytecodeCount":9,"sources":[{"source":1,"begin":766,"end":885},{"source":1,"begin":924,"end":925},{"source":1,"begin":949,"end":1002},{"source":1,"begin":994,"end":1001},{"source":1,"begin":985,"end":991},{"source":1,"begin":974,"end":983},{"source":1,"begin":970,"end":992}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1045,"bytecodeCount":10,"sources":[{"source":1,"begin":545,"end":684},{"source":1,"begin":591,"end":596},{"source":1,"begin":629,"end":635},{"source":1,"begin":616,"end":636},{"source":1,"begin":607,"end":636},{"source":1,"begin":645,"end":678},{"source":1,"begin":672,"end":677}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1022,"bytecodeCount":5,"sources":[{"source":1,"begin":417,"end":539},{"source":1,"begin":490,"end":514},{"source":1,"begin":508,"end":513}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1012,"bytecodeCount":9,"sources":[{"source":1,"begin":334,"end":411},{"source":1,"begin":371,"end":378},{"source":1,"begin":400,"end":405},{"source":1,"begin":389,"end":405}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1031,"bytecodeCount":5,"sources":[{"source":1,"begin":490,"end":514},{"source":1,"begin":483,"end":488},{"source":1,"begin":480,"end":515},{"source":1,"begin":470,"end":533}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1042,"bytecodeCount":3,"sources":[{"source":1,"begin":470,"end":533},{"source":1,"begin":417,"end":539}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1060,"bytecodeCount":6,"sources":[{"source":1,"begin":645,"end":678},{"source":1,"begin":545,"end":684}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1102,"bytecodeCount":9,"sources":[{"source":1,"begin":949,"end":1002},{"source":1,"begin":939,"end":1002},{"source":1,"begin":895,"end":1012},{"source":1,"begin":690,"end":1019}]}}
		AnnotationCmd:144 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":102,"bytecodeCount":3,"sources":[{"source":0,"begin":319,"end":396}]}}
		AnnotationCmd:149 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":193,"bytecodeCount":37,"sources":[{"source":0,"begin":319,"end":396},{"source":0,"begin":367,"end":371},{"source":0,"begin":367,"end":380},{"source":0,"begin":381,"end":382},{"source":0,"begin":384,"end":385},{"source":0,"begin":384,"end":388},{"source":0,"begin":386,"end":387},{"source":0,"begin":367,"end":389}]}}
		AssignExpCmd:150 R53:46 Apply(hash_3_keccak:bif Apply(skey_basic:bif 0x40) Apply(skey_basic:bif 0x0) Apply(skey_basic:bif 0x0))
		AnnotationCmd:144 JSON{"key":{"name":"init.reorder.fence","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		AssignExpCmd:151 tacMCANON0!!55:1 Store(tacMCANON0havocme2376!!5:0 0x80 0x870bf39300000000000000000000000000000000000000000000000000000000 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2440,"bytecodeCount":14,"sources":[{"source":1,"begin":11159,"end":11578},{"source":1,"begin":11323,"end":11327},{"source":1,"begin":11361,"end":11364},{"source":1,"begin":11350,"end":11359},{"source":1,"begin":11346,"end":11365},{"source":1,"begin":11338,"end":11365},{"source":1,"begin":11375,"end":11446},{"source":1,"begin":11443,"end":11444},{"source":1,"begin":11432,"end":11441},{"source":1,"begin":11428,"end":11445},{"source":1,"begin":11419,"end":11425}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1810,"bytecodeCount":5,"sources":[{"source":1,"begin":5941,"end":6059},{"source":1,"begin":6028,"end":6052},{"source":1,"begin":6046,"end":6051}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1012,"bytecodeCount":9,"sources":[{"source":1,"begin":334,"end":411},{"source":1,"begin":371,"end":378},{"source":1,"begin":400,"end":405},{"source":1,"begin":389,"end":405}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1819,"bytecodeCount":6,"sources":[{"source":1,"begin":6028,"end":6052},{"source":1,"begin":6023,"end":6026},{"source":1,"begin":6016,"end":6053},{"source":1,"begin":5941,"end":6059}]}}
		AssignExpCmd:144 R56:47 tacCalldatabufCANON0@1:153
		AssignExpCmd:151 tacMCANON0!!57:1 Store(tacMCANON0!!55:1 0x84 tacCalldatabufCANON0@1:153 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2462,"bytecodeCount":8,"sources":[{"source":1,"begin":11375,"end":11446},{"source":1,"begin":11456,"end":11571},{"source":1,"begin":11567,"end":11569},{"source":1,"begin":11556,"end":11565},{"source":1,"begin":11552,"end":11570},{"source":1,"begin":11543,"end":11549}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2361,"bytecodeCount":15,"sources":[{"source":1,"begin":10315,"end":11153},{"source":1,"begin":10455,"end":10461},{"source":1,"begin":10450,"end":10453},{"source":1,"begin":10446,"end":10462},{"source":1,"begin":10488,"end":10489},{"source":1,"begin":10563,"end":10567},{"source":1,"begin":10556,"end":10561},{"source":1,"begin":10552,"end":10568},{"source":1,"begin":10581,"end":10685},{"source":1,"begin":10679,"end":10683},{"source":1,"begin":10674,"end":10677},{"source":1,"begin":10670,"end":10684},{"source":1,"begin":10656,"end":10668}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2161,"bytecodeCount":15,"sources":[{"source":1,"begin":8485,"end":10243},{"source":1,"begin":8613,"end":8617},{"source":1,"begin":8608,"end":8611},{"source":1,"begin":8604,"end":8618},{"source":1,"begin":8644,"end":8645},{"source":1,"begin":8716,"end":8720},{"source":1,"begin":8709,"end":8714},{"source":1,"begin":8705,"end":8721},{"source":1,"begin":8699,"end":8722},{"source":1,"begin":8686,"end":8722},{"source":1,"begin":8755,"end":8810},{"source":1,"begin":8800,"end":8809}]}}
		AssignExpCmd:154 R59:48 AnnotationExp(Select(CANON35!!9:12 R53:155 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Words","numWords":"0"}}]}})
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R59","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"x","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":0}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1848,"bytecodeCount":7,"sources":[{"source":1,"begin":6269,"end":6435},{"source":1,"begin":6338,"end":6343},{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6417,"end":6427}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1862,"bytecodeCount":3,"sources":[{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6363,"end":6429}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1838,"bytecodeCount":9,"sources":[{"source":1,"begin":6173,"end":6263},{"source":1,"begin":6223,"end":6230},{"source":1,"begin":6252,"end":6257},{"source":1,"begin":6241,"end":6257}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1867,"bytecodeCount":7,"sources":[{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6354,"end":6429},{"source":1,"begin":6269,"end":6435}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2182,"bytecodeCount":8,"sources":[{"source":1,"begin":8755,"end":8810},{"source":1,"begin":8823,"end":8886},{"source":1,"begin":8880,"end":8884},{"source":1,"begin":8875,"end":8878},{"source":1,"begin":8871,"end":8885},{"source":1,"begin":8857,"end":8869}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1874,"bytecodeCount":5,"sources":[{"source":1,"begin":6441,"end":6549},{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6536,"end":6541}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1012,"bytecodeCount":9,"sources":[{"source":1,"begin":334,"end":411},{"source":1,"begin":371,"end":378},{"source":1,"begin":400,"end":405},{"source":1,"begin":389,"end":405}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1883,"bytecodeCount":6,"sources":[{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6513,"end":6516},{"source":1,"begin":6506,"end":6543},{"source":1,"begin":6441,"end":6549}]}}
		AssignExpCmd:151 tacMCANON0!!61:1 Store(tacMCANON0!!57:1 0xa4 R59:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2195,"bytecodeCount":12,"sources":[{"source":1,"begin":8823,"end":8886},{"source":1,"begin":8655,"end":8896},{"source":1,"begin":8967,"end":8971},{"source":1,"begin":8960,"end":8965},{"source":1,"begin":8956,"end":8972},{"source":1,"begin":8950,"end":8973},{"source":1,"begin":8937,"end":8973},{"source":1,"begin":9006,"end":9061},{"source":1,"begin":9051,"end":9060}]}}
		AssignExpCmd:151 R62:48 Apply(skey_add:bif R53:46 0x1)
		AssignExpCmd:156 R63:48 AnnotationExp(Select(CANON38!!11:6 R62:157 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"20"}}]}})
		AssumeExpCmd Le(R63:48 0xffffffffffffffffffffffffffffffffffffffff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R63","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"y","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":1}}}
		AssignExpCmd:156 R64:48 AnnotationExp(Select(CANON39!!12:7 R62:158 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"34"}}]}})
		AssumeExpCmd Le(R64:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R64","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"z1","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":1}}}
		AssignExpCmd:156 R65:48 AnnotationExp(Select(CANON40!!13:13 R62:159 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"35"}}]}})
		AssumeExpCmd Le(R65:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R65","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"z2","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":1}}}
		AssignExpCmd:156 R66:48 AnnotationExp(Select(CANON41!!14:14 R62:160 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"36"}}]}})
		AssumeExpCmd Le(R66:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R66","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b1","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":1}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1921,"bytecodeCount":7,"sources":[{"source":1,"begin":6700,"end":6866},{"source":1,"begin":6769,"end":6774},{"source":1,"begin":6794,"end":6860},{"source":1,"begin":6825,"end":6859},{"source":1,"begin":6848,"end":6858}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1935,"bytecodeCount":3,"sources":[{"source":1,"begin":6825,"end":6859},{"source":1,"begin":6794,"end":6860}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1889,"bytecodeCount":11,"sources":[{"source":1,"begin":6555,"end":6694},{"source":1,"begin":6605,"end":6612},{"source":1,"begin":6645,"end":6687},{"source":1,"begin":6638,"end":6643},{"source":1,"begin":6634,"end":6688},{"source":1,"begin":6623,"end":6688}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1940,"bytecodeCount":7,"sources":[{"source":1,"begin":6794,"end":6860},{"source":1,"begin":6785,"end":6860},{"source":1,"begin":6700,"end":6866}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2212,"bytecodeCount":8,"sources":[{"source":1,"begin":9006,"end":9061},{"source":1,"begin":9074,"end":9137},{"source":1,"begin":9131,"end":9135},{"source":1,"begin":9126,"end":9129},{"source":1,"begin":9122,"end":9136},{"source":1,"begin":9108,"end":9120}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1947,"bytecodeCount":5,"sources":[{"source":1,"begin":6872,"end":6980},{"source":1,"begin":6949,"end":6973},{"source":1,"begin":6967,"end":6972}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1288,"bytecodeCount":6,"sources":[{"source":1,"begin":2119,"end":2215},{"source":1,"begin":2156,"end":2163},{"source":1,"begin":2185,"end":2209},{"source":1,"begin":2203,"end":2208}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1256,"bytecodeCount":11,"sources":[{"source":1,"begin":1987,"end":2113},{"source":1,"begin":2024,"end":2031},{"source":1,"begin":2064,"end":2106},{"source":1,"begin":2057,"end":2062},{"source":1,"begin":2053,"end":2107},{"source":1,"begin":2042,"end":2107}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1299,"bytecodeCount":7,"sources":[{"source":1,"begin":2185,"end":2209},{"source":1,"begin":2174,"end":2209},{"source":1,"begin":2119,"end":2215}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1956,"bytecodeCount":6,"sources":[{"source":1,"begin":6949,"end":6973},{"source":1,"begin":6944,"end":6947},{"source":1,"begin":6937,"end":6974},{"source":1,"begin":6872,"end":6980}]}}
		AssignExpCmd:151 tacMCANON0!!68:1 Store(tacMCANON0!!61:1 0xc4 R63:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2225,"bytecodeCount":6,"sources":[{"source":1,"begin":9074,"end":9137},{"source":1,"begin":8906,"end":9147},{"source":1,"begin":9210,"end":9264},{"source":1,"begin":9254,"end":9263}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1988,"bytecodeCount":7,"sources":[{"source":1,"begin":7203,"end":7368},{"source":1,"begin":7271,"end":7276},{"source":1,"begin":7296,"end":7362},{"source":1,"begin":7325,"end":7361},{"source":1,"begin":7350,"end":7360}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1962,"bytecodeCount":11,"sources":[{"source":1,"begin":6986,"end":7092},{"source":1,"begin":7030,"end":7038},{"source":1,"begin":7079,"end":7084},{"source":1,"begin":7074,"end":7077},{"source":1,"begin":7070,"end":7085},{"source":1,"begin":7049,"end":7085}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2002,"bytecodeCount":3,"sources":[{"source":1,"begin":7325,"end":7361},{"source":1,"begin":7296,"end":7362}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1975,"bytecodeCount":11,"sources":[{"source":1,"begin":7098,"end":7197},{"source":1,"begin":7146,"end":7153},{"source":1,"begin":7186,"end":7190},{"source":1,"begin":7179,"end":7184},{"source":1,"begin":7175,"end":7191},{"source":1,"begin":7164,"end":7191}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2007,"bytecodeCount":7,"sources":[{"source":1,"begin":7296,"end":7362},{"source":1,"begin":7287,"end":7362},{"source":1,"begin":7203,"end":7368}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2235,"bytecodeCount":8,"sources":[{"source":1,"begin":9210,"end":9264},{"source":1,"begin":9277,"end":9336},{"source":1,"begin":9330,"end":9334},{"source":1,"begin":9325,"end":9328},{"source":1,"begin":9321,"end":9335},{"source":1,"begin":9307,"end":9319}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2014,"bytecodeCount":5,"sources":[{"source":1,"begin":7374,"end":7476},{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7463,"end":7468}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1350,"bytecodeCount":11,"sources":[{"source":1,"begin":2494,"end":2580},{"source":1,"begin":2529,"end":2536},{"source":1,"begin":2569,"end":2573},{"source":1,"begin":2562,"end":2567},{"source":1,"begin":2558,"end":2574},{"source":1,"begin":2547,"end":2574}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2023,"bytecodeCount":6,"sources":[{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7442,"end":7445},{"source":1,"begin":7435,"end":7470},{"source":1,"begin":7374,"end":7476}]}}
		AssignExpCmd:151 tacMCANON0!!70:1 Store(tacMCANON0!!68:1 0xe4 R64:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2248,"bytecodeCount":6,"sources":[{"source":1,"begin":9277,"end":9336},{"source":1,"begin":9157,"end":9346},{"source":1,"begin":9409,"end":9463},{"source":1,"begin":9453,"end":9462}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2042,"bytecodeCount":7,"sources":[{"source":1,"begin":7594,"end":7759},{"source":1,"begin":7662,"end":7667},{"source":1,"begin":7687,"end":7753},{"source":1,"begin":7716,"end":7752},{"source":1,"begin":7741,"end":7751}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2029,"bytecodeCount":11,"sources":[{"source":1,"begin":7482,"end":7588},{"source":1,"begin":7526,"end":7534},{"source":1,"begin":7575,"end":7580},{"source":1,"begin":7570,"end":7573},{"source":1,"begin":7566,"end":7581},{"source":1,"begin":7545,"end":7581}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2056,"bytecodeCount":3,"sources":[{"source":1,"begin":7716,"end":7752},{"source":1,"begin":7687,"end":7753}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1975,"bytecodeCount":11,"sources":[{"source":1,"begin":7098,"end":7197},{"source":1,"begin":7146,"end":7153},{"source":1,"begin":7186,"end":7190},{"source":1,"begin":7179,"end":7184},{"source":1,"begin":7175,"end":7191},{"source":1,"begin":7164,"end":7191}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2061,"bytecodeCount":7,"sources":[{"source":1,"begin":7687,"end":7753},{"source":1,"begin":7678,"end":7753},{"source":1,"begin":7594,"end":7759}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2258,"bytecodeCount":8,"sources":[{"source":1,"begin":9409,"end":9463},{"source":1,"begin":9476,"end":9535},{"source":1,"begin":9529,"end":9533},{"source":1,"begin":9524,"end":9527},{"source":1,"begin":9520,"end":9534},{"source":1,"begin":9506,"end":9518}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2014,"bytecodeCount":5,"sources":[{"source":1,"begin":7374,"end":7476},{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7463,"end":7468}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1350,"bytecodeCount":11,"sources":[{"source":1,"begin":2494,"end":2580},{"source":1,"begin":2529,"end":2536},{"source":1,"begin":2569,"end":2573},{"source":1,"begin":2562,"end":2567},{"source":1,"begin":2558,"end":2574},{"source":1,"begin":2547,"end":2574}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2023,"bytecodeCount":6,"sources":[{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7442,"end":7445},{"source":1,"begin":7435,"end":7470},{"source":1,"begin":7374,"end":7476}]}}
		AssignExpCmd:151 tacMCANON0!!72:1 Store(tacMCANON0!!70:1 0x104 R65:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2271,"bytecodeCount":6,"sources":[{"source":1,"begin":9476,"end":9535},{"source":1,"begin":9356,"end":9545},{"source":1,"begin":9608,"end":9661},{"source":1,"begin":9651,"end":9660}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2094,"bytecodeCount":7,"sources":[{"source":1,"begin":7981,"end":8144},{"source":1,"begin":8048,"end":8053},{"source":1,"begin":8073,"end":8138},{"source":1,"begin":8101,"end":8137},{"source":1,"begin":8126,"end":8136}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2068,"bytecodeCount":11,"sources":[{"source":1,"begin":7765,"end":7871},{"source":1,"begin":7809,"end":7817},{"source":1,"begin":7858,"end":7863},{"source":1,"begin":7853,"end":7856},{"source":1,"begin":7849,"end":7864},{"source":1,"begin":7828,"end":7864}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2108,"bytecodeCount":3,"sources":[{"source":1,"begin":8101,"end":8137},{"source":1,"begin":8073,"end":8138}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2081,"bytecodeCount":11,"sources":[{"source":1,"begin":7877,"end":7975},{"source":1,"begin":7924,"end":7931},{"source":1,"begin":7964,"end":7968},{"source":1,"begin":7957,"end":7962},{"source":1,"begin":7953,"end":7969},{"source":1,"begin":7942,"end":7969}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2113,"bytecodeCount":7,"sources":[{"source":1,"begin":8073,"end":8138},{"source":1,"begin":8064,"end":8138},{"source":1,"begin":7981,"end":8144}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2281,"bytecodeCount":8,"sources":[{"source":1,"begin":9608,"end":9661},{"source":1,"begin":9674,"end":9731},{"source":1,"begin":9725,"end":9729},{"source":1,"begin":9720,"end":9723},{"source":1,"begin":9716,"end":9730},{"source":1,"begin":9702,"end":9714}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2120,"bytecodeCount":5,"sources":[{"source":1,"begin":8150,"end":8249},{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8236,"end":8241}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1407,"bytecodeCount":11,"sources":[{"source":1,"begin":2851,"end":2941},{"source":1,"begin":2885,"end":2892},{"source":1,"begin":2928,"end":2933},{"source":1,"begin":2921,"end":2934},{"source":1,"begin":2914,"end":2935},{"source":1,"begin":2903,"end":2935}]}}
		AssignExpCmd:144 R74:39 Ite(Eq(R66:48 0x0 ) 0x0 0x1 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2129,"bytecodeCount":6,"sources":[{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8216,"end":8219},{"source":1,"begin":8209,"end":8243},{"source":1,"begin":8150,"end":8249}]}}
		AssignExpCmd:151 tacMCANON0!!76:1 Store(tacMCANON0!!72:1 0x124 R74:39 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2294,"bytecodeCount":12,"sources":[{"source":1,"begin":9674,"end":9731},{"source":1,"begin":9555,"end":9741},{"source":1,"begin":9813,"end":9817},{"source":1,"begin":9806,"end":9811},{"source":1,"begin":9802,"end":9818},{"source":1,"begin":9796,"end":9819},{"source":1,"begin":9783,"end":9819},{"source":1,"begin":9852,"end":9907},{"source":1,"begin":9897,"end":9906}]}}
		AssignExpCmd:144 R77:48 Apply(skey_add:bif R62:48 0x1)
		AssignExpCmd:161 R78:48 AnnotationExp(Select(CANON46!!15:18 R77:162 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Words","numWords":"2"}}]}})
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R78","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"x2","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":2}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1848,"bytecodeCount":7,"sources":[{"source":1,"begin":6269,"end":6435},{"source":1,"begin":6338,"end":6343},{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6417,"end":6427}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1862,"bytecodeCount":3,"sources":[{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6363,"end":6429}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1838,"bytecodeCount":9,"sources":[{"source":1,"begin":6173,"end":6263},{"source":1,"begin":6223,"end":6230},{"source":1,"begin":6252,"end":6257},{"source":1,"begin":6241,"end":6257}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1867,"bytecodeCount":7,"sources":[{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6354,"end":6429},{"source":1,"begin":6269,"end":6435}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2311,"bytecodeCount":8,"sources":[{"source":1,"begin":9852,"end":9907},{"source":1,"begin":9920,"end":9983},{"source":1,"begin":9977,"end":9981},{"source":1,"begin":9972,"end":9975},{"source":1,"begin":9968,"end":9982},{"source":1,"begin":9954,"end":9966}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1874,"bytecodeCount":5,"sources":[{"source":1,"begin":6441,"end":6549},{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6536,"end":6541}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1012,"bytecodeCount":9,"sources":[{"source":1,"begin":334,"end":411},{"source":1,"begin":371,"end":378},{"source":1,"begin":400,"end":405},{"source":1,"begin":389,"end":405}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1883,"bytecodeCount":6,"sources":[{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6513,"end":6516},{"source":1,"begin":6506,"end":6543},{"source":1,"begin":6441,"end":6549}]}}
		AssignExpCmd:151 tacMCANON0!!80:1 Store(tacMCANON0!!76:1 0x144 R78:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2324,"bytecodeCount":12,"sources":[{"source":1,"begin":9920,"end":9983},{"source":1,"begin":9751,"end":9993},{"source":1,"begin":10065,"end":10069},{"source":1,"begin":10058,"end":10063},{"source":1,"begin":10054,"end":10070},{"source":1,"begin":10048,"end":10071},{"source":1,"begin":10035,"end":10071},{"source":1,"begin":10104,"end":10156},{"source":1,"begin":10146,"end":10155}]}}
		AssignExpCmd:144 R81:48 Apply(skey_add:bif R77:48 0x1)
		AssignExpCmd:163 R82:48 AnnotationExp(Select(CANON48!!16:19 R81:164 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"60"}}]}})
		AssumeExpCmd Le(R82:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R82","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b2","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.None"}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2135,"bytecodeCount":7,"sources":[{"source":1,"begin":8255,"end":8415},{"source":1,"begin":8321,"end":8326},{"source":1,"begin":8346,"end":8409},{"source":1,"begin":8374,"end":8408},{"source":1,"begin":8397,"end":8407}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2149,"bytecodeCount":3,"sources":[{"source":1,"begin":8374,"end":8408},{"source":1,"begin":8346,"end":8409}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2081,"bytecodeCount":11,"sources":[{"source":1,"begin":7877,"end":7975},{"source":1,"begin":7924,"end":7931},{"source":1,"begin":7964,"end":7968},{"source":1,"begin":7957,"end":7962},{"source":1,"begin":7953,"end":7969},{"source":1,"begin":7942,"end":7969}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2154,"bytecodeCount":7,"sources":[{"source":1,"begin":8346,"end":8409},{"source":1,"begin":8337,"end":8409},{"source":1,"begin":8255,"end":8415}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2341,"bytecodeCount":8,"sources":[{"source":1,"begin":10104,"end":10156},{"source":1,"begin":10169,"end":10226},{"source":1,"begin":10220,"end":10224},{"source":1,"begin":10215,"end":10218},{"source":1,"begin":10211,"end":10225},{"source":1,"begin":10197,"end":10209}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2120,"bytecodeCount":5,"sources":[{"source":1,"begin":8150,"end":8249},{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8236,"end":8241}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1407,"bytecodeCount":11,"sources":[{"source":1,"begin":2851,"end":2941},{"source":1,"begin":2885,"end":2892},{"source":1,"begin":2928,"end":2933},{"source":1,"begin":2921,"end":2934},{"source":1,"begin":2914,"end":2935},{"source":1,"begin":2903,"end":2935}]}}
		AssignExpCmd:144 R84:39 Ite(Eq(R82:48 0x0 ) 0x0 0x1 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2129,"bytecodeCount":6,"sources":[{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8216,"end":8219},{"source":1,"begin":8209,"end":8243},{"source":1,"begin":8150,"end":8249}]}}
		AssignExpCmd:151 tacMCANON0!!86:1 Store(tacMCANON0!!80:1 0x164 R84:39 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2354,"bytecodeCount":7,"sources":[{"source":1,"begin":10169,"end":10226},{"source":1,"begin":10003,"end":10236},{"source":1,"begin":8582,"end":10243},{"source":1,"begin":8485,"end":10243}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2384,"bytecodeCount":12,"sources":[{"source":1,"begin":10581,"end":10685},{"source":1,"begin":10499,"end":10695},{"source":1,"begin":10769,"end":10773},{"source":1,"begin":10762,"end":10767},{"source":1,"begin":10758,"end":10774},{"source":1,"begin":10787,"end":10891},{"source":1,"begin":10885,"end":10889},{"source":1,"begin":10880,"end":10883},{"source":1,"begin":10876,"end":10890},{"source":1,"begin":10862,"end":10874}]}}
		AssignExpCmd:144 R87:56 Apply(skey_add:bif R81:48 0x1)
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2161,"bytecodeCount":15,"sources":[{"source":1,"begin":8485,"end":10243},{"source":1,"begin":8613,"end":8617},{"source":1,"begin":8608,"end":8611},{"source":1,"begin":8604,"end":8618},{"source":1,"begin":8644,"end":8645},{"source":1,"begin":8716,"end":8720},{"source":1,"begin":8709,"end":8714},{"source":1,"begin":8705,"end":8721},{"source":1,"begin":8699,"end":8722},{"source":1,"begin":8686,"end":8722},{"source":1,"begin":8755,"end":8810},{"source":1,"begin":8800,"end":8809}]}}
		AssignExpCmd:165 R89:48 AnnotationExp(Select(CANON50!!17:33 R87:166 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Words","numWords":"4"}}]}})
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R89","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"x","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s2","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":3}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1848,"bytecodeCount":7,"sources":[{"source":1,"begin":6269,"end":6435},{"source":1,"begin":6338,"end":6343},{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6417,"end":6427}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1862,"bytecodeCount":3,"sources":[{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6363,"end":6429}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1838,"bytecodeCount":9,"sources":[{"source":1,"begin":6173,"end":6263},{"source":1,"begin":6223,"end":6230},{"source":1,"begin":6252,"end":6257},{"source":1,"begin":6241,"end":6257}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1867,"bytecodeCount":7,"sources":[{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6354,"end":6429},{"source":1,"begin":6269,"end":6435}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2182,"bytecodeCount":8,"sources":[{"source":1,"begin":8755,"end":8810},{"source":1,"begin":8823,"end":8886},{"source":1,"begin":8880,"end":8884},{"source":1,"begin":8875,"end":8878},{"source":1,"begin":8871,"end":8885},{"source":1,"begin":8857,"end":8869}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1874,"bytecodeCount":5,"sources":[{"source":1,"begin":6441,"end":6549},{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6536,"end":6541}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1012,"bytecodeCount":9,"sources":[{"source":1,"begin":334,"end":411},{"source":1,"begin":371,"end":378},{"source":1,"begin":400,"end":405},{"source":1,"begin":389,"end":405}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1883,"bytecodeCount":6,"sources":[{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6513,"end":6516},{"source":1,"begin":6506,"end":6543},{"source":1,"begin":6441,"end":6549}]}}
		AssignExpCmd:151 tacMCANON0!!91:1 Store(tacMCANON0!!86:1 0x184 R89:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2195,"bytecodeCount":12,"sources":[{"source":1,"begin":8823,"end":8886},{"source":1,"begin":8655,"end":8896},{"source":1,"begin":8967,"end":8971},{"source":1,"begin":8960,"end":8965},{"source":1,"begin":8956,"end":8972},{"source":1,"begin":8950,"end":8973},{"source":1,"begin":8937,"end":8973},{"source":1,"begin":9006,"end":9061},{"source":1,"begin":9051,"end":9060}]}}
		AssignExpCmd:151 R92:48 Apply(skey_add:bif R87:56 0x1)
		AssignExpCmd:167 R93:48 AnnotationExp(Select(CANON52!!18:34 R92:168 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"a0"}}]}})
		AssumeExpCmd Le(R93:48 0xffffffffffffffffffffffffffffffffffffffff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R93","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"y","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s2","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":4}}}
		AssignExpCmd:167 R94:48 AnnotationExp(Select(CANON53!!19:35 R92:169 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"b4"}}]}})
		AssumeExpCmd Le(R94:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R94","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"z1","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s2","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":4}}}
		AssignExpCmd:167 R95:48 AnnotationExp(Select(CANON54!!20:36 R92:170 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"b5"}}]}})
		AssumeExpCmd Le(R95:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R95","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"z2","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s2","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":4}}}
		AssignExpCmd:167 R96:48 AnnotationExp(Select(CANON55!!21:37 R92:171 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"b6"}}]}})
		AssumeExpCmd Le(R96:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R96","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b1","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s2","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":4}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1921,"bytecodeCount":7,"sources":[{"source":1,"begin":6700,"end":6866},{"source":1,"begin":6769,"end":6774},{"source":1,"begin":6794,"end":6860},{"source":1,"begin":6825,"end":6859},{"source":1,"begin":6848,"end":6858}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1935,"bytecodeCount":3,"sources":[{"source":1,"begin":6825,"end":6859},{"source":1,"begin":6794,"end":6860}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1889,"bytecodeCount":11,"sources":[{"source":1,"begin":6555,"end":6694},{"source":1,"begin":6605,"end":6612},{"source":1,"begin":6645,"end":6687},{"source":1,"begin":6638,"end":6643},{"source":1,"begin":6634,"end":6688},{"source":1,"begin":6623,"end":6688}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1940,"bytecodeCount":7,"sources":[{"source":1,"begin":6794,"end":6860},{"source":1,"begin":6785,"end":6860},{"source":1,"begin":6700,"end":6866}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2212,"bytecodeCount":8,"sources":[{"source":1,"begin":9006,"end":9061},{"source":1,"begin":9074,"end":9137},{"source":1,"begin":9131,"end":9135},{"source":1,"begin":9126,"end":9129},{"source":1,"begin":9122,"end":9136},{"source":1,"begin":9108,"end":9120}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1947,"bytecodeCount":5,"sources":[{"source":1,"begin":6872,"end":6980},{"source":1,"begin":6949,"end":6973},{"source":1,"begin":6967,"end":6972}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1288,"bytecodeCount":6,"sources":[{"source":1,"begin":2119,"end":2215},{"source":1,"begin":2156,"end":2163},{"source":1,"begin":2185,"end":2209},{"source":1,"begin":2203,"end":2208}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1256,"bytecodeCount":11,"sources":[{"source":1,"begin":1987,"end":2113},{"source":1,"begin":2024,"end":2031},{"source":1,"begin":2064,"end":2106},{"source":1,"begin":2057,"end":2062},{"source":1,"begin":2053,"end":2107},{"source":1,"begin":2042,"end":2107}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1299,"bytecodeCount":7,"sources":[{"source":1,"begin":2185,"end":2209},{"source":1,"begin":2174,"end":2209},{"source":1,"begin":2119,"end":2215}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1956,"bytecodeCount":6,"sources":[{"source":1,"begin":6949,"end":6973},{"source":1,"begin":6944,"end":6947},{"source":1,"begin":6937,"end":6974},{"source":1,"begin":6872,"end":6980}]}}
		AssignExpCmd:151 tacMCANON0!!98:1 Store(tacMCANON0!!91:1 0x1a4 R93:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2225,"bytecodeCount":6,"sources":[{"source":1,"begin":9074,"end":9137},{"source":1,"begin":8906,"end":9147},{"source":1,"begin":9210,"end":9264},{"source":1,"begin":9254,"end":9263}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1988,"bytecodeCount":7,"sources":[{"source":1,"begin":7203,"end":7368},{"source":1,"begin":7271,"end":7276},{"source":1,"begin":7296,"end":7362},{"source":1,"begin":7325,"end":7361},{"source":1,"begin":7350,"end":7360}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1962,"bytecodeCount":11,"sources":[{"source":1,"begin":6986,"end":7092},{"source":1,"begin":7030,"end":7038},{"source":1,"begin":7079,"end":7084},{"source":1,"begin":7074,"end":7077},{"source":1,"begin":7070,"end":7085},{"source":1,"begin":7049,"end":7085}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2002,"bytecodeCount":3,"sources":[{"source":1,"begin":7325,"end":7361},{"source":1,"begin":7296,"end":7362}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1975,"bytecodeCount":11,"sources":[{"source":1,"begin":7098,"end":7197},{"source":1,"begin":7146,"end":7153},{"source":1,"begin":7186,"end":7190},{"source":1,"begin":7179,"end":7184},{"source":1,"begin":7175,"end":7191},{"source":1,"begin":7164,"end":7191}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2007,"bytecodeCount":7,"sources":[{"source":1,"begin":7296,"end":7362},{"source":1,"begin":7287,"end":7362},{"source":1,"begin":7203,"end":7368}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2235,"bytecodeCount":8,"sources":[{"source":1,"begin":9210,"end":9264},{"source":1,"begin":9277,"end":9336},{"source":1,"begin":9330,"end":9334},{"source":1,"begin":9325,"end":9328},{"source":1,"begin":9321,"end":9335},{"source":1,"begin":9307,"end":9319}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2014,"bytecodeCount":5,"sources":[{"source":1,"begin":7374,"end":7476},{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7463,"end":7468}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1350,"bytecodeCount":11,"sources":[{"source":1,"begin":2494,"end":2580},{"source":1,"begin":2529,"end":2536},{"source":1,"begin":2569,"end":2573},{"source":1,"begin":2562,"end":2567},{"source":1,"begin":2558,"end":2574},{"source":1,"begin":2547,"end":2574}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2023,"bytecodeCount":6,"sources":[{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7442,"end":7445},{"source":1,"begin":7435,"end":7470},{"source":1,"begin":7374,"end":7476}]}}
		AssignExpCmd:151 tacMCANON0!!100:1 Store(tacMCANON0!!98:1 0x1c4 R94:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2248,"bytecodeCount":6,"sources":[{"source":1,"begin":9277,"end":9336},{"source":1,"begin":9157,"end":9346},{"source":1,"begin":9409,"end":9463},{"source":1,"begin":9453,"end":9462}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2042,"bytecodeCount":7,"sources":[{"source":1,"begin":7594,"end":7759},{"source":1,"begin":7662,"end":7667},{"source":1,"begin":7687,"end":7753},{"source":1,"begin":7716,"end":7752},{"source":1,"begin":7741,"end":7751}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2029,"bytecodeCount":11,"sources":[{"source":1,"begin":7482,"end":7588},{"source":1,"begin":7526,"end":7534},{"source":1,"begin":7575,"end":7580},{"source":1,"begin":7570,"end":7573},{"source":1,"begin":7566,"end":7581},{"source":1,"begin":7545,"end":7581}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2056,"bytecodeCount":3,"sources":[{"source":1,"begin":7716,"end":7752},{"source":1,"begin":7687,"end":7753}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1975,"bytecodeCount":11,"sources":[{"source":1,"begin":7098,"end":7197},{"source":1,"begin":7146,"end":7153},{"source":1,"begin":7186,"end":7190},{"source":1,"begin":7179,"end":7184},{"source":1,"begin":7175,"end":7191},{"source":1,"begin":7164,"end":7191}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2061,"bytecodeCount":7,"sources":[{"source":1,"begin":7687,"end":7753},{"source":1,"begin":7678,"end":7753},{"source":1,"begin":7594,"end":7759}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2258,"bytecodeCount":8,"sources":[{"source":1,"begin":9409,"end":9463},{"source":1,"begin":9476,"end":9535},{"source":1,"begin":9529,"end":9533},{"source":1,"begin":9524,"end":9527},{"source":1,"begin":9520,"end":9534},{"source":1,"begin":9506,"end":9518}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2014,"bytecodeCount":5,"sources":[{"source":1,"begin":7374,"end":7476},{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7463,"end":7468}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1350,"bytecodeCount":11,"sources":[{"source":1,"begin":2494,"end":2580},{"source":1,"begin":2529,"end":2536},{"source":1,"begin":2569,"end":2573},{"source":1,"begin":2562,"end":2567},{"source":1,"begin":2558,"end":2574},{"source":1,"begin":2547,"end":2574}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2023,"bytecodeCount":6,"sources":[{"source":1,"begin":7447,"end":7469},{"source":1,"begin":7442,"end":7445},{"source":1,"begin":7435,"end":7470},{"source":1,"begin":7374,"end":7476}]}}
		AssignExpCmd:151 tacMCANON0!!102:1 Store(tacMCANON0!!100:1 0x1e4 R95:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2271,"bytecodeCount":6,"sources":[{"source":1,"begin":9476,"end":9535},{"source":1,"begin":9356,"end":9545},{"source":1,"begin":9608,"end":9661},{"source":1,"begin":9651,"end":9660}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2094,"bytecodeCount":7,"sources":[{"source":1,"begin":7981,"end":8144},{"source":1,"begin":8048,"end":8053},{"source":1,"begin":8073,"end":8138},{"source":1,"begin":8101,"end":8137},{"source":1,"begin":8126,"end":8136}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2068,"bytecodeCount":11,"sources":[{"source":1,"begin":7765,"end":7871},{"source":1,"begin":7809,"end":7817},{"source":1,"begin":7858,"end":7863},{"source":1,"begin":7853,"end":7856},{"source":1,"begin":7849,"end":7864},{"source":1,"begin":7828,"end":7864}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2108,"bytecodeCount":3,"sources":[{"source":1,"begin":8101,"end":8137},{"source":1,"begin":8073,"end":8138}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2081,"bytecodeCount":11,"sources":[{"source":1,"begin":7877,"end":7975},{"source":1,"begin":7924,"end":7931},{"source":1,"begin":7964,"end":7968},{"source":1,"begin":7957,"end":7962},{"source":1,"begin":7953,"end":7969},{"source":1,"begin":7942,"end":7969}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2113,"bytecodeCount":7,"sources":[{"source":1,"begin":8073,"end":8138},{"source":1,"begin":8064,"end":8138},{"source":1,"begin":7981,"end":8144}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2281,"bytecodeCount":8,"sources":[{"source":1,"begin":9608,"end":9661},{"source":1,"begin":9674,"end":9731},{"source":1,"begin":9725,"end":9729},{"source":1,"begin":9720,"end":9723},{"source":1,"begin":9716,"end":9730},{"source":1,"begin":9702,"end":9714}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2120,"bytecodeCount":5,"sources":[{"source":1,"begin":8150,"end":8249},{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8236,"end":8241}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1407,"bytecodeCount":11,"sources":[{"source":1,"begin":2851,"end":2941},{"source":1,"begin":2885,"end":2892},{"source":1,"begin":2928,"end":2933},{"source":1,"begin":2921,"end":2934},{"source":1,"begin":2914,"end":2935},{"source":1,"begin":2903,"end":2935}]}}
		AssignExpCmd:144 R104:39 Ite(Eq(R96:48 0x0 ) 0x0 0x1 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2129,"bytecodeCount":6,"sources":[{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8216,"end":8219},{"source":1,"begin":8209,"end":8243},{"source":1,"begin":8150,"end":8249}]}}
		AssignExpCmd:151 tacMCANON0!!106:1 Store(tacMCANON0!!102:1 0x204 R104:39 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2294,"bytecodeCount":12,"sources":[{"source":1,"begin":9674,"end":9731},{"source":1,"begin":9555,"end":9741},{"source":1,"begin":9813,"end":9817},{"source":1,"begin":9806,"end":9811},{"source":1,"begin":9802,"end":9818},{"source":1,"begin":9796,"end":9819},{"source":1,"begin":9783,"end":9819},{"source":1,"begin":9852,"end":9907},{"source":1,"begin":9897,"end":9906}]}}
		AssignExpCmd:144 R107:48 Apply(skey_add:bif R92:48 0x1)
		AssignExpCmd:172 R108:48 AnnotationExp(Select(CANON60!!22:73 R107:173 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Words","numWords":"6"}}]}})
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R108","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"x2","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s2","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.Id","id":5}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1848,"bytecodeCount":7,"sources":[{"source":1,"begin":6269,"end":6435},{"source":1,"begin":6338,"end":6343},{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6417,"end":6427}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1862,"bytecodeCount":3,"sources":[{"source":1,"begin":6394,"end":6428},{"source":1,"begin":6363,"end":6429}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1838,"bytecodeCount":9,"sources":[{"source":1,"begin":6173,"end":6263},{"source":1,"begin":6223,"end":6230},{"source":1,"begin":6252,"end":6257},{"source":1,"begin":6241,"end":6257}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1867,"bytecodeCount":7,"sources":[{"source":1,"begin":6363,"end":6429},{"source":1,"begin":6354,"end":6429},{"source":1,"begin":6269,"end":6435}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2311,"bytecodeCount":8,"sources":[{"source":1,"begin":9852,"end":9907},{"source":1,"begin":9920,"end":9983},{"source":1,"begin":9977,"end":9981},{"source":1,"begin":9972,"end":9975},{"source":1,"begin":9968,"end":9982},{"source":1,"begin":9954,"end":9966}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1874,"bytecodeCount":5,"sources":[{"source":1,"begin":6441,"end":6549},{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6536,"end":6541}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1012,"bytecodeCount":9,"sources":[{"source":1,"begin":334,"end":411},{"source":1,"begin":371,"end":378},{"source":1,"begin":400,"end":405},{"source":1,"begin":389,"end":405}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1883,"bytecodeCount":6,"sources":[{"source":1,"begin":6518,"end":6542},{"source":1,"begin":6513,"end":6516},{"source":1,"begin":6506,"end":6543},{"source":1,"begin":6441,"end":6549}]}}
		AssignExpCmd:151 tacMCANON0!!110:1 Store(tacMCANON0!!106:1 0x224 R108:48 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2324,"bytecodeCount":12,"sources":[{"source":1,"begin":9920,"end":9983},{"source":1,"begin":9751,"end":9993},{"source":1,"begin":10065,"end":10069},{"source":1,"begin":10058,"end":10063},{"source":1,"begin":10054,"end":10070},{"source":1,"begin":10048,"end":10071},{"source":1,"begin":10035,"end":10071},{"source":1,"begin":10104,"end":10156},{"source":1,"begin":10146,"end":10155}]}}
		AssignExpCmd:144 R111:48 Apply(skey_add:bif R107:48 0x1)
		AssignExpCmd:174 R112:48 AnnotationExp(Select(CANON62!!23:74 R111:175 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"e0"}}]}})
		AssumeExpCmd Le(R112:48 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R112","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1003}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b2","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s2","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.None"}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2135,"bytecodeCount":7,"sources":[{"source":1,"begin":8255,"end":8415},{"source":1,"begin":8321,"end":8326},{"source":1,"begin":8346,"end":8409},{"source":1,"begin":8374,"end":8408},{"source":1,"begin":8397,"end":8407}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2149,"bytecodeCount":3,"sources":[{"source":1,"begin":8374,"end":8408},{"source":1,"begin":8346,"end":8409}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2081,"bytecodeCount":11,"sources":[{"source":1,"begin":7877,"end":7975},{"source":1,"begin":7924,"end":7931},{"source":1,"begin":7964,"end":7968},{"source":1,"begin":7957,"end":7962},{"source":1,"begin":7953,"end":7969},{"source":1,"begin":7942,"end":7969}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2154,"bytecodeCount":7,"sources":[{"source":1,"begin":8346,"end":8409},{"source":1,"begin":8337,"end":8409},{"source":1,"begin":8255,"end":8415}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2341,"bytecodeCount":8,"sources":[{"source":1,"begin":10104,"end":10156},{"source":1,"begin":10169,"end":10226},{"source":1,"begin":10220,"end":10224},{"source":1,"begin":10215,"end":10218},{"source":1,"begin":10211,"end":10225},{"source":1,"begin":10197,"end":10209}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2120,"bytecodeCount":5,"sources":[{"source":1,"begin":8150,"end":8249},{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8236,"end":8241}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1407,"bytecodeCount":11,"sources":[{"source":1,"begin":2851,"end":2941},{"source":1,"begin":2885,"end":2892},{"source":1,"begin":2928,"end":2933},{"source":1,"begin":2921,"end":2934},{"source":1,"begin":2914,"end":2935},{"source":1,"begin":2903,"end":2935}]}}
		AssignExpCmd:144 R114:39 Ite(Eq(R112:48 0x0 ) 0x0 0x1 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2129,"bytecodeCount":6,"sources":[{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8216,"end":8219},{"source":1,"begin":8209,"end":8243},{"source":1,"begin":8150,"end":8249}]}}
		AssignExpCmd:151 tacMCANON0!!116:1 Store(tacMCANON0!!110:1 0x244 R114:39 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2354,"bytecodeCount":7,"sources":[{"source":1,"begin":10169,"end":10226},{"source":1,"begin":10003,"end":10236},{"source":1,"begin":8582,"end":10243},{"source":1,"begin":8485,"end":10243}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2402,"bytecodeCount":12,"sources":[{"source":1,"begin":10787,"end":10891},{"source":1,"begin":10705,"end":10901},{"source":1,"begin":10973,"end":10977},{"source":1,"begin":10966,"end":10971},{"source":1,"begin":10962,"end":10978},{"source":1,"begin":10956,"end":10979},{"source":1,"begin":10943,"end":10979},{"source":1,"begin":11012,"end":11064},{"source":1,"begin":11054,"end":11063}]}}
		AssignExpCmd:144 R117:56 Apply(skey_add:bif R111:48 0x1)
		AssignExpCmd:176 R118:56 AnnotationExp(Select(CANON64!!24:84 R117:177 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R10","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"hashResult":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R53","tag":{"#class":"tac.Tag.UserDefined.UninterpretedSort","name":"skey"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1018}]}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"100"}}]}})
		AssumeExpCmd Le(R118:56 0xff )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R118","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1009}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b3","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"linkableStorageReadId":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.LoadSnippet.None"}}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2135,"bytecodeCount":7,"sources":[{"source":1,"begin":8255,"end":8415},{"source":1,"begin":8321,"end":8326},{"source":1,"begin":8346,"end":8409},{"source":1,"begin":8374,"end":8408},{"source":1,"begin":8397,"end":8407}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1825,"bytecodeCount":11,"sources":[{"source":1,"begin":6065,"end":6167},{"source":1,"begin":6107,"end":6115},{"source":1,"begin":6154,"end":6159},{"source":1,"begin":6151,"end":6152},{"source":1,"begin":6147,"end":6160},{"source":1,"begin":6126,"end":6160}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2149,"bytecodeCount":3,"sources":[{"source":1,"begin":8374,"end":8408},{"source":1,"begin":8346,"end":8409}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2081,"bytecodeCount":11,"sources":[{"source":1,"begin":7877,"end":7975},{"source":1,"begin":7924,"end":7931},{"source":1,"begin":7964,"end":7968},{"source":1,"begin":7957,"end":7962},{"source":1,"begin":7953,"end":7969},{"source":1,"begin":7942,"end":7969}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2154,"bytecodeCount":7,"sources":[{"source":1,"begin":8346,"end":8409},{"source":1,"begin":8337,"end":8409},{"source":1,"begin":8255,"end":8415}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2419,"bytecodeCount":8,"sources":[{"source":1,"begin":11012,"end":11064},{"source":1,"begin":11077,"end":11136},{"source":1,"begin":11128,"end":11134},{"source":1,"begin":11123,"end":11126},{"source":1,"begin":11119,"end":11135},{"source":1,"begin":11105,"end":11117}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2120,"bytecodeCount":5,"sources":[{"source":1,"begin":8150,"end":8249},{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8236,"end":8241}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":1407,"bytecodeCount":11,"sources":[{"source":1,"begin":2851,"end":2941},{"source":1,"begin":2885,"end":2892},{"source":1,"begin":2928,"end":2933},{"source":1,"begin":2921,"end":2934},{"source":1,"begin":2914,"end":2935},{"source":1,"begin":2903,"end":2935}]}}
		AssignExpCmd:144 R120:60 Ite(Eq(R118:56 0x0 ) 0x0 0x1 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2129,"bytecodeCount":6,"sources":[{"source":1,"begin":8221,"end":8242},{"source":1,"begin":8216,"end":8219},{"source":1,"begin":8209,"end":8243},{"source":1,"begin":8150,"end":8249}]}}
		AssignExpCmd:151 tacMCANON0!!122:1 Store(tacMCANON0!!116:1 0x264 R120:60 )
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2433,"bytecodeCount":7,"sources":[{"source":1,"begin":11077,"end":11136},{"source":1,"begin":10911,"end":11146},{"source":1,"begin":10424,"end":11153},{"source":1,"begin":10315,"end":11153}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":2475,"bytecodeCount":7,"sources":[{"source":1,"begin":11456,"end":11571},{"source":1,"begin":11159,"end":11578}]}}
		AnnotationCmd:152 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":269,"bytecodeCount":17,"sources":[{"source":0,"begin":367,"end":389}]}}
		AssignExpCmd:151 R123:66 0x80
		AssignExpCmd:151 R124:67 0x204
		AssignExpCmd:151 R125:68 Select(tacExtcodesize!!4:11 Apply(to_skey:bif R28:178) )
		AssumeExpCmd Ge(R125:68 0x1 )
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.RawStorageAccess.WithLocSym","isLoad":true,"loc":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R28","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.contract.sym.addr.name","type":"java.lang.String","erasureStrategy":"Erased"},"value":"TestContract"},{"key":{"name":"tac.contract.sym.addr","type":"java.math.BigInteger","erasureStrategy":"Erased"},"value":"ce4604a0000000000000000000000001"},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1021}]},"contractInstance":"ce4604a0000000000000000000000001","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R125","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry","name":"L","maybeTACKeywordOrdinal":45}},{"key":{"name":"tac.stack.height","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":1012}]},"storageType":null,"range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}}}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":2,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"content":"this.workOnS1(x, m[0])"}}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":2}}
		AnnotationCmd:151 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":295,"bytecodeCount":9,"sources":[{"source":0,"begin":367,"end":389}]}}
		AssignHavocCmd:151 R126:68
		AnnotationCmd:151 JSON{"key":{"name":"tac.decompiler.call-start","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		AssignHavocCmd:151 tacReturndata!!127:16
		JumpCmd 2_0_0_2_0_1
	}
	Block 2_0_0_2_0_1 Succ [3_0_0_1_0_0] {
		AnnotationCmd JSON{"key":{"name":"call.trace.external.summary.start","type":"analysis.icfg.SummaryStack$SummaryStart$External","erasureStrategy":"CallTrace"},"value":"rO0ABXNyADBhbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5U3RhcnQkRXh0ZXJuYWyjNkk2r+9AZAIABUwADmFwcGxpZWRTdW1tYXJ5dAAsTGFuYWx5c2lzL2ljZmcvU3VtbWFyaXphdGlvbiRBcHBsaWVkU3VtbWFyeTtMAAhjYWxsTm9kZXQAFUx2Yy9kYXRhL0NhbGxTdW1tYXJ5O0wAF2NhbGxSZXNvbHV0aW9uVGFibGVJbmZvdAA2THJlcG9ydC9jYWxscmVzb2x1dGlvbi9DYWxsUmVzb2x1dGlvblRhYmxlU3VtbWFyeUluZm87TAALY2FsbFNpdGVTcmN0ABVMdmMvZGF0YS9UQUNNZXRhSW5mbztMAAdzdXBwb3J0dAAPTGphdmEvdXRpbC9TZXQ7eHIAJ2FuYWx5c2lzLmljZmcuU3VtbWFyeVN0YWNrJFN1bW1hcnlTdGFydM6P29O9R0c9AgAAeHBzcgA3YW5hbHlzaXMuaWNmZy5TdW1tYXJpemF0aW9uJEFwcGxpZWRTdW1tYXJ5JE1ldGhvZHNCbG9ja8QZaUG9nkK8AgACTAAMc3BlY0NhbGxTdW1tdAAuTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRFeHByZXNzaWJsZUluQ1ZMO0wAEHN1bW1hcml6ZWRNZXRob2R0ABtMc3BlYy9DVkwkU3VtbWFyeVNpZ25hdHVyZTt4cHNyAB9zcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnkkRXhwiLXACP96VR8CAAdMAANleHB0ABRMc3BlYy9jdmxhc3QvQ1ZMRXhwO0wADGV4cGVjdGVkVHlwZXQAEExqYXZhL3V0aWwvTGlzdDtMAAlmdW5QYXJhbXNxAH4ADkwABXJhbmdldAANTHV0aWxzL1JhbmdlO0wABXNjb3BldAAWTHNwZWMvY3ZsYXN0L0NWTFNjb3BlO0wAEXN1bW1hcml6YXRpb25Nb2RldAAvTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRTdW1tYXJpemF0aW9uTW9kZTtMAAp3aXRoQ2xhdXNldAAsTHNwZWMvY3ZsYXN0L1NwZWNDYWxsU3VtbWFyeSRFeHAkV2l0aENsYXVzZTt4cgAsc3BlYy5jdmxhc3QuU3BlY0NhbGxTdW1tYXJ5JEV4cHJlc3NpYmxlSW5DVkw5jBEFxNlONwIAAHhyABtzcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnmf4QieXcWlAQIAAHhwc3IAJ3NwZWMuY3ZsYXN0LkNWTEV4cCRBcHBseUV4cCRDVkxGdW5jdGlvbghf8sf20DA6AgAFWgAIbm9SZXZlcnRMAARhcmdzcQB+AA5MAAJpZHQAEkxqYXZhL2xhbmcvU3RyaW5nO0wAF21ldGhvZElkV2l0aENhbGxDb250ZXh0dAAdTHNwZWMvY3ZsYXN0L1NwZWNEZWNsYXJhdGlvbjtMAAN0YWd0ABdMc3BlYy9jdmxhc3QvQ1ZMRXhwVGFnO3hyABtzcGVjLmN2bGFzdC5DVkxFeHAkQXBwbHlFeHAF3JlNR+1SuwIAAHhyACFzcGVjLmN2bGFzdC5DVkxFeHAkQXBwbGljYXRpb25FeHAEe7zFegP5fQIAAHhyABJzcGVjLmN2bGFzdC5DVkxFeHAB+J/cNeGTiAIAAHhwAXNyABNqYXZhLnV0aWwuQXJyYXlMaXN0eIHSHZnHYZ0DAAFJAARzaXpleHAAAAACdwQAAAACc3IAHnNwZWMuY3ZsYXN0LkNWTEV4cCRWYXJpYWJsZUV4cJ0ULkp52IKNAgAETAACaWRxAH4AF0wADG9yaWdpbmFsTmFtZXEAfgAXTAADdGFncQB+ABlMAA10d29TdGF0ZUluZGV4dAAbTHNwZWMvY3ZsYXN0L1R3b1N0YXRlSW5kZXg7eHEAfgAcdAABeHEAfgAjc3IAFXNwZWMuY3ZsYXN0LkNWTEV4cFRhZ9WLKphaC/tTAgAFWgAJaGFzUGFyZW5zTAAKYW5ub3RhdGlvbnQAIkxzcGVjL2N2bGFzdC9FeHByZXNzaW9uQW5ub3RhdGlvbjtMAAVyYW5nZXEAfgAPTAAFc2NvcGVxAH4AEEwABHR5cGV0ABVMc3BlYy9jdmxhc3QvQ1ZMVHlwZTt4cABwc3IAEXV0aWxzLlJhbmdlJFJhbmdlelevcoxEsQYCAANMAANlbmR0ABZMdXRpbHMvU291cmNlUG9zaXRpb247TAAIc3BlY0ZpbGVxAH4AF0wABXN0YXJ0cQB+ACl4cgALdXRpbHMuUmFuZ2XoA/TylWV/VwIAAHhwc3IAFHV0aWxzLlNvdXJjZVBvc2l0aW9ulfTn1OqZxI0CAAJJAA5jaGFyQnl0ZU9mZnNldEkABGxpbmV4cAAAAFUAAAADdAAJdGVzdC5zcGVjc3EAfgAsAAAAVAAAAANzcgAUc3BlYy5jdmxhc3QuQ1ZMU2NvcGUiyWBY1B1dVAIAA0wAFmhhc2hDb2RlQ2FjaGUkZGVsZWdhdGV0AA1Ma290bGluL0xhenk7TAAKaW5uZXJTY29wZXEAfgAQTAAKc2NvcGVTdGFja3EAfgAOeHBzcgAaa290bGluLkluaXRpYWxpemVkTGF6eUltcGx7x3/xICqBjQIAAUwABXZhbHVldAASTGphdmEvbGFuZy9PYmplY3Q7eHBzcgARamF2YS5sYW5nLkludGVnZXIS4qCk94GHOAIAAUkABXZhbHVleHIAEGphdmEubGFuZy5OdW1iZXKGrJUdC5TgiwIAAHhwzPGoX3NxAH4AMHNxAH4AM3NxAH4ANk5njWFzcQB+ADBzcQB+ADNzcQB+ADYAAAAfcHNyABxrb3RsaW4uY29sbGVjdGlvbnMuRW1wdHlMaXN0mW/H0KfgYDICAAB4cHNyACNqYXZhLnV0aWwuQ29sbGVjdGlvbnMkU2luZ2xldG9uTGlzdCrvKRA8p5uXAgABTAAHZWxlbWVudHEAfgA0eHBzcgAmc3BlYy5jdmxhc3QuQ1ZMU2NvcGUkSXRlbSRBc3RTY29wZUl0ZW2Hm6f3BtWhkwIAAHhyABlzcGVjLmN2bGFzdC5DVkxTY29wZSRJdGVtLwOv/543VkUCAAB4cHNxAH4AHgAAAAJ3BAAAAAJxAH4ARXNyACtzcGVjLmN2bGFzdC5DVkxTY29wZSRJdGVtJEV4cHJlc3Npb25TdW1tYXJ5DzManVpfqWgCAAFJAAdzY29wZUlkeHIAKXNwZWMuY3ZsYXN0LkNWTFNjb3BlJEl0ZW0kQVNURWxlbWVudFNjb3BlUquPEVHkIpYCAAFMAAdlbGVtZW50dAAaTHNwZWMvY3ZsYXN0L0NyZWF0ZXNTY29wZTt4cQB+AERzcQB+AAxzcgAlc3BlYy5jdmxhc3QuQ1ZMRXhwJFVucmVzb2x2ZWRBcHBseUV4cDU+F4IbuX3IAgAIWgAMaW52b2tlSXNTYWZlWgANaW52b2tlSXNXaG9sZUwABGFyZ3NxAH4ADkwABGJhc2VxAH4ADUwADWludm9rZVN0b3JhZ2V0ACBMc3BlYy9jdmxhc3QvQ1ZMRXhwJFZhcmlhYmxlRXhwO0wACG1ldGhvZElkcQB+ABdMAAN0YWdxAH4AGUwADXR3b1N0YXRlSW5kZXhxAH4AIXhxAH4AGwEAc3EAfgAeAAAAAncEAAAAAnNxAH4AIHEAfgAjcQB+ACNzcQB+ACQAcHEAfgArcQB+ADJwfnIAGXNwZWMuY3ZsYXN0LlR3b1N0YXRlSW5kZXgAAAAAAAAAABIAAHhyAA5qYXZhLmxhbmcuRW51bQAAAAAAAAAAEgAAeHB0AAdORUlUSEVSc3EAfgAgdAABc3EAfgBXc3EAfgAkAHBzcQB+AChzcQB+ACwAAABYAAAAA3EAfgAuc3EAfgAsAAAAVwAAAANxAH4AMnBxAH4AVHhwc3EAfgAgdAALbGFzdFN0b3JhZ2VxAH4AXXNxAH4AJABwc3IAEXV0aWxzLlJhbmdlJEVtcHR5xIMekl54ldcCAAFMAAdjb21tZW50cQB+ABd4cQB+ACp0ABJlbXB0eSBzdG9yYWdlIHR5cGVxAH4AMnBxAH4AVHQAEXdvcmtPblNDb21wbGV4Q1ZMc3EAfgAkAHBzcQB+AChzcQB+ACwAAABZAAAAA3EAfgAuc3EAfgAsAAAAQgAAAANxAH4AMnBxAH4AVHBzcQB+AB4AAAACdwQAAAACc3IAGXNwZWMuY3ZsYXN0LlZNUGFyYW0kTmFtZWQAXezwjrrQjQIABEwABG5hbWVxAH4AF0wADG9yaWdpbmFsTmFtZXEAfgAXTAAFcmFuZ2VxAH4AD0wABnZtVHlwZXQALkxzcGVjL2N2bGFzdC90eXBlZGVzY3JpcHRvcnMvVk1UeXBlRGVzY3JpcHRvcjt4cgATc3BlYy5jdmxhc3QuVk1QYXJhbaA5qID7MF6/AgAAeHBxAH4AI3EAfgAjc3EAfgAoc3EAfgAsAAAAHAAAAANxAH4ALnNxAH4ALAAAABYAAAADc3IAM3NwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRVSW50S6h6LEsweg4lAgABSQAIYml0d2lkdGh4cgBEc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJEVWTUlzb21vcnBoaWNWYWx1ZVR5cGWW45V3at3xfwIAAHhyADpzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkRVZNVmFsdWVUeXBlEOTS9aivN+ECAAB4cgAtc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yXlYd3MaOPugCAAB4cAAAAQBzcQB+AGhxAH4AV3EAfgBXc3EAfgAoc3EAfgAsAAAANAAAAANxAH4ALnNxAH4ALAAAAB4AAAADc3IAQXNwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRFVk1TdHJ1Y3REZXNjcmlwdG9ypg3XjxMA4UoCAARMAAtjYW5vbmljYWxJZHEAfgAXTAAGZmllbGRzcQB+AA5MAAhsb2NhdGlvbnQAMkxzcGVjL2N2bGFzdC90eXBlZGVzY3JpcHRvcnMvRVZNTG9jYXRpb25TcGVjaWZpZXI7TAAEbmFtZXEAfgAXeHEAfgBydAAlVGVzdENvbnRyYWN0LnNvbHxUZXN0Q29udHJhY3QuQ29tcGxleHNxAH4AHgAAAAN3BAAAAANzcgBQc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJEVWTVN0cnVjdERlc2NyaXB0b3IkRVZNU3RydWN0RW50cnkfXd8E+GvhmwIAAkwACWZpZWxkTmFtZXEAfgAXTAAJZmllbGRUeXBldAAvTHNwZWMvY3ZsYXN0L3R5cGVkZXNjcmlwdG9ycy9FVk1UeXBlRGVzY3JpcHRvcjt4cHQAAnMxc3EAfgB4dAAkVGVzdENvbnRyYWN0LnNvbHxUZXN0Q29udHJhY3QuU2ltcGxlc3EAfgAeAAAAB3cEAAAAB3NxAH4AfXEAfgAjc3EAfgBvAAABAHNxAH4AfXQAAXlzcgA1c3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJGFkZHJlc3PEsTBR9nlqCAIAAHhxAH4AcHNxAH4AfXQAAnoxc3EAfgBvAAAACHNxAH4AfXQAAnoyc3EAfgBvAAAACHNxAH4AfXQAAmIxc3IAMnNwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRib29sBUKy4CN7H8kCAAB4cQB+AHBzcQB+AH10AAJ4MnNxAH4AbwAAAQBzcQB+AH10AAJiMnEAfgCTeHB0ABNUZXN0Q29udHJhY3QuU2ltcGxlc3EAfgB9dAACczJzcQB+AHhxAH4AgnNxAH4AHgAAAAd3BAAAAAdzcQB+AH1xAH4AI3NxAH4AbwAAAQBzcQB+AH1xAH4Ah3EAfgCJc3EAfgB9cQB+AItzcQB+AG8AAAAIc3EAfgB9cQB+AI5zcQB+AG8AAAAIc3EAfgB9cQB+AJFxAH4Ak3NxAH4AfXEAfgCVc3EAfgBvAAABAHNxAH4AfXEAfgCYcQB+AJN4cHEAfgCZc3EAfgB9dAACYjNxAH4Ak3hwdAAUVGVzdENvbnRyYWN0LkNvbXBsZXh4c3EAfgAoc3EAfgAsAAAAWQAAAANxAH4ALnNxAH4ALAAAAEIAAAADcQB+ADJ+cgAtc3BlYy5jdmxhc3QuU3BlY0NhbGxTdW1tYXJ5JFN1bW1hcml6YXRpb25Nb2RlAAAAAAAAAAASAAB4cQB+AFN0AANBTExwAAAAAHhzcgAWc3BlYy5jdmxhc3QuQ1ZMVHlwZSRWTaOrOy0dfN99AgACTAAHY29udGV4dHQAK0xzcGVjL2N2bGFzdC90eXBlZGVzY3JpcHRvcnMvRnJvbVZNQ29udGV4dDtMAApkZXNjcmlwdG9ycQB+AGl4cgATc3BlYy5jdmxhc3QuQ1ZMVHlwZXQxE5W3wWVQAgAAeHBzcgBDc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkZyb21WTUNvbnRleHQkRXh0ZXJuYWxTdW1tYXJ5QXJnQmluZGluZ8J0TOn4TD97AgAAeHIAKXNwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5Gcm9tVk1Db250ZXh0xdrxhvd38GUCAAB4cHEAfgBzcQB+AFRzcQB+ACBxAH4AV3EAfgBXc3EAfgAkAHBxAH4AWXEAfgAyc3EAfgCycQB+ALhxAH4AenEAfgBUeHEAfgBic3IAG3NwZWMuY3ZsYXN0LlNwZWNEZWNsYXJhdGlvbo0W9A88qKG3AgABTAAIbWV0aG9kSWRxAH4AF3hwcQB+AGJzcQB+ACQAc3IAF3NwZWMuY3ZsYXN0LkNWTEZ1bmN0aW9uLlnVqImHyGECAAlMAAVibG9ja3EAfgAOTAANZGVjbGFyYXRpb25JZHEAfgAXTAASZnVuY3Rpb25JZGVudGlmaWVycQB+ABhMAApwYXJhbVR5cGVzcQB+AA5MAAZwYXJhbXNxAH4ADkwABXJhbmdlcQB+AA9MAARyZXRzdAAhTHNwZWMvY3ZsYXN0L0NWTFR5cGUkUHVyZUNWTFR5cGU7TAAFc2NvcGVxAH4AEEwAD3R5cGVEZXNjcmlwdGlvbnEAfgAXeHBzcQB+AB4AAAAEdwQAAAAEc3IAH3NwZWMuY3ZsYXN0LkNWTENtZCRTaW1wbGUkSGF2b2NBvsIPTDaAXQIABEwAC2Fzc3VtaW5nRXhwcQB+AA1MAAVyYW5nZXEAfgAPTAAFc2NvcGVxAH4AEEwAB3RhcmdldHNxAH4ADnhyABlzcGVjLmN2bGFzdC5DVkxDbWQkU2ltcGxlgP+RSwrmk0gCAAB4cgASc3BlYy5jdmxhc3QuQ1ZMQ21kfU+09keTqJICAAB4cHBzcQB+AChzcQB+ACwAAAAiAAAACHEAfgAuc3EAfgAsAAAABAAAAAhzcQB+ADBzcQB+ADNzcQB+ADbM8al2cQB+ADlzcQB+AB4AAAACdwQAAAACcQB+AEVzcgAuc3BlYy5jdmxhc3QuQ1ZMU2NvcGUkSXRlbSRDVkxGdW5jdGlvblNjb3BlSXRlbXtbyEBhg0o5AgABSQAHc2NvcGVJZHhxAH4ASHNxAH4Av3NxAH4AHgAAAAR3BAAAAARzcQB+AMNwcQB+AMdxAH4AynNxAH4AHgAAAAF3BAAAAAFzcgAhc3BlYy5jdmxhc3QuQ1ZMRXhwJEZpZWxkU2VsZWN0RXhwUzuAAXzaWa4CAANMAAlmaWVsZE5hbWVxAH4AF0wACXN0cnVjdEV4cHEAfgANTAADdGFncQB+ABl4cQB+ABxxAH4AkXNxAH4A1HEAfgCAc3IAIHNwZWMuY3ZsYXN0LkNWTEV4cCRBcnJheURlcmVmRXhw5CTb4GwIYAYCAANMAAVhcnJheXEAfgANTAAFaW5kZXhxAH4ADUwAA3RhZ3EAfgAZeHEAfgAcc3EAfgDUdAABbXNxAH4AIHQADHRlc3RDb250cmFjdHEAfgDcc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAWAAAACHEAfgAuc3EAfgAsAAAACgAAAAhxAH4AynBxAH4AVHNxAH4AJABwc3EAfgAoc3EAfgAsAAAAGAAAAAhxAH4ALnNxAH4ALAAAAAoAAAAIcQB+AMpwc3IAJXNwZWMuY3ZsYXN0LkNWTEV4cCRDb25zdGFudCROdW1iZXJMaXQAXZb+I542BQIAA0wAAW50ABZMamF2YS9tYXRoL0JpZ0ludGVnZXI7TAAJcHJpbnRIaW50cQB+ABdMAAN0YWdxAH4AGXhyABtzcGVjLmN2bGFzdC5DVkxFeHAkQ29uc3RhbnS7VbSpZ6efmwIAAHhxAH4AHHNyABRqYXZhLm1hdGguQmlnSW50ZWdlcoz8nx+pO/sdAwAGSQAIYml0Q291bnRJAAliaXRMZW5ndGhJABNmaXJzdE5vbnplcm9CeXRlTnVtSQAMbG93ZXN0U2V0Qml0SQAGc2lnbnVtWwAJbWFnbml0dWRldAACW0J4cQB+ADf///////////////7////+AAAAAHVyAAJbQqzzF/gGCFTgAgAAeHAAAAAAeHQAAjEwc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAaAAAACHEAfgAuc3EAfgAsAAAAGQAAAAhxAH4AynBzcQB+ACQAcHNxAH4AKHNxAH4ALAAAABsAAAAIcQB+AC5zcQB+ACwAAAAKAAAACHEAfgDKcHNxAH4AJABwc3EAfgAoc3EAfgAsAAAAHgAAAAhxAH4ALnNxAH4ALAAAAAoAAAAIcQB+AMpwc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAhAAAACHEAfgAuc3EAfgAsAAAACgAAAAhxAH4AynB4c3IAKnNwZWMuY3ZsYXN0LkNWTENtZCRTaW1wbGUkQXNzdW1lQ21kJEFzc3VtZawoaSHEDsCkAgAGWgANY29tZXNGcm9tU3BlY1oAEGludmFyaWFudFByZUNvbmRMAAtkZXNjcmlwdGlvbnEAfgAXTAADZXhwcQB+AA1MAAVyYW5nZXEAfgAPTAAFc2NvcGVxAH4AEHhyACNzcGVjLmN2bGFzdC5DVkxDbWQkU2ltcGxlJEFzc3VtZUNtZG9e2sLcjguEAgAAeHEAfgDEAQBwc3IAIXNwZWMuY3ZsYXN0LkNWTEV4cCRSZWxvcEV4cCRFcUV4cEgOUbefVtTKAgADTAABbHEAfgANTAABcnEAfgANTAADdGFncQB+ABl4cgAbc3BlYy5jdmxhc3QuQ1ZMRXhwJFJlbG9wRXhw1P7NRFjvu6ICAAB4cQB+ABxzcQB+ANRxAH4AkXNxAH4A1HEAfgCAc3EAfgDXc3EAfgDUcQB+ANpzcQB+ACBxAH4A3HEAfgDcc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAYAAAACXEAfgAuc3EAfgAsAAAADAAAAAlxAH4AynBxAH4AVHNxAH4AJABwc3EAfgAoc3EAfgAsAAAAGgAAAAlxAH4ALnNxAH4ALAAAAAwAAAAJcQB+AMpwc3EAfgDlcQB+AOtxAH4A7nNxAH4AJABwc3EAfgAoc3EAfgAsAAAAHAAAAAlxAH4ALnNxAH4ALAAAABsAAAAJcQB+AMpwc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAdAAAACXEAfgAuc3EAfgAsAAAADAAAAAlxAH4AynBzcQB+ACQAcHNxAH4AKHNxAH4ALAAAACAAAAAJcQB+AC5zcQB+ACwAAAAMAAAACXEAfgDKcHNxAH4AJABwc3EAfgAoc3EAfgAsAAAAIwAAAAlxAH4ALnNxAH4ALAAAAAwAAAAJcQB+AMpwc3IAL3NwZWMuY3ZsYXN0LkNWTEV4cCRSZWxvcEV4cCRBcml0aFJlbG9wRXhwJEd0RXhwiloskl81tasCAANMAAFscQB+AA1MAAFycQB+AA1MAAN0YWdxAH4AGXhyAClzcGVjLmN2bGFzdC5DVkxFeHAkUmVsb3BFeHAkQXJpdGhSZWxvcEV4cI7opCkt6stnAgAAeHEAfgEDc3EAfgAgcQB+ACNxAH4AI3NxAH4AJABwc3EAfgAoc3EAfgAsAAAAKQAAAAlxAH4ALnNxAH4ALAAAACgAAAAJcQB+AMpwcQB+AFRzcQB+AOVzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAEDeHEAfgDuc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAtAAAACXEAfgAuc3EAfgAsAAAALAAAAAlxAH4AynBzcQB+ACQBcHNxAH4AKHNxAH4ALAAAAC0AAAAJcQB+AC5zcQB+ACwAAAAoAAAACXEAfgDKcHNxAH4AJABwc3EAfgAoc3EAfgAsAAAALgAAAAlxAH4ALnNxAH4ALAAAAAwAAAAJcQB+AMpwc3EAfgAoc3EAfgAsAAAALwAAAAlxAH4ALnNxAH4ALAAAAAQAAAAJcQB+AMpzcQB+AMNwc3EAfgAoc3EAfgAsAAAAHwAAAApxAH4ALnNxAH4ALAAAAAQAAAAKcQB+AMpzcQB+AB4AAAABdwQAAAABc3EAfgDUcQB+AKpzcQB+ANdzcQB+ANRxAH4A2nNxAH4AIHEAfgDccQB+ANxzcQB+ACQAcHNxAH4AKHNxAH4ALAAAABYAAAAKcQB+AC5zcQB+ACwAAAAKAAAACnEAfgDKcHEAfgBUc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAYAAAACnEAfgAuc3EAfgAsAAAACgAAAApxAH4AynBzcQB+AOVxAH4A63EAfgDuc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAaAAAACnEAfgAuc3EAfgAsAAAAGQAAAApxAH4AynBzcQB+ACQAcHNxAH4AKHNxAH4ALAAAABsAAAAKcQB+AC5zcQB+ACwAAAAKAAAACnEAfgDKcHNxAH4AJABwc3EAfgAoc3EAfgAsAAAAHgAAAApxAH4ALnNxAH4ALAAAAAoAAAAKcQB+AMpweHNxAH4A/wEAcHNxAH4BAnNxAH4A1HEAfgCqc3EAfgDXc3EAfgDUcQB+ANpzcQB+ACBxAH4A3HEAfgDcc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAYAAAAC3EAfgAuc3EAfgAsAAAADAAAAAtxAH4AynBxAH4AVHNxAH4AJABwc3EAfgAoc3EAfgAsAAAAGgAAAAtxAH4ALnNxAH4ALAAAAAwAAAALcQB+AMpwc3EAfgDlcQB+AOtxAH4A7nNxAH4AJABwc3EAfgAoc3EAfgAsAAAAHAAAAAtxAH4ALnNxAH4ALAAAABsAAAALcQB+AMpwc3EAfgAkAHBzcQB+AChzcQB+ACwAAAAdAAAAC3EAfgAuc3EAfgAsAAAADAAAAAtxAH4AynBzcQB+ACQAcHNxAH4AKHNxAH4ALAAAACAAAAALcQB+AC5zcQB+ACwAAAAMAAAAC3EAfgDKcHNxAH4BI3NxAH4AIHEAfgAjcQB+ACNzcQB+ACQAcHNxAH4AKHNxAH4ALAAAACYAAAALcQB+AC5zcQB+ACwAAAAlAAAAC3EAfgDKcHEAfgBUc3EAfgDlc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAABBXhxAH4A7nNxAH4AJABwc3EAfgAoc3EAfgAsAAAAKgAAAAtxAH4ALnNxAH4ALAAAACkAAAALcQB+AMpwc3EAfgAkAXBzcQB+AChzcQB+ACwAAAAqAAAAC3EAfgAuc3EAfgAsAAAAJQAAAAtxAH4AynBzcQB+ACQAcHNxAH4AKHNxAH4ALAAAACsAAAALcQB+AC5zcQB+ACwAAAAMAAAAC3EAfgDKcHNxAH4AKHNxAH4ALAAAACwAAAALcQB+AC5zcQB+ACwAAAAEAAAAC3EAfgDKeHEAfgBic3EAfgC8cQB+AGJzcQB+AB4AAAACdwQAAAACc3IAL3NwZWMuY3ZsYXN0LkNWTFR5cGUkUHVyZUNWTFR5cGUkUHJpbWl0aXZlJFVJbnRLuQuajikSRikCAAJJAAhiaXRXaWR0aEkAAWt4cgApc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRQcmltaXRpdmUKm9v/NH7COwIAAHhyAB9zcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBl/Qa0FlO2KLECAAB4cQB+ALQAAAEAAAABAHNyACZzcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBlJFN0cnVjdDVJoRRpEzmDAgACTAAGZmllbGRzcQB+AA5MAARuYW1lcQB+ABd4cQB+AZJzcQB+AB4AAAADdwQAAAADc3IAMnNwZWMuY3ZsYXN0LkNWTFR5cGUkUHVyZUNWTFR5cGUkU3RydWN0JFN0cnVjdEVudHJ5Mx8aM/226g0CAAJMAAdjdmxUeXBlcQB+AMBMAAlmaWVsZE5hbWVxAH4AF3hwc3EAfgGUc3EAfgAeAAAAB3cEAAAAB3NxAH4Bl3NxAH4BkAAAAQAAAAEAcQB+ACNzcQB+AZdzcgA7c3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRQcmltaXRpdmUkQWNjb3VudElkZW50aWZpZXIgRQpE/AKbcQIAAHhxAH4BkXEAfgCHc3EAfgGXc3EAfgGQAAAACAAAAAhxAH4Ai3NxAH4Bl3NxAH4BkAAAAAgAAAAIcQB+AI5zcQB+AZdzcgAuc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRQcmltaXRpdmUkQm9vbNurwWjYMLLPAgAAeHEAfgGRcQB+AJFzcQB+AZdzcQB+AZAAAAEAAAABAHEAfgCVc3EAfgGXcQB+AaZxAH4AmHhxAH4AmXEAfgCAc3EAfgGXc3EAfgGUc3EAfgAeAAAAB3cEAAAAB3NxAH4Bl3NxAH4BkAAAAQAAAAEAcQB+ACNzcQB+AZdxAH4Bn3EAfgCHc3EAfgGXc3EAfgGQAAAACAAAAAhxAH4Ai3NxAH4Bl3NxAH4BkAAAAAgAAAAIcQB+AI5zcQB+AZdxAH4BpnEAfgCRc3EAfgGXc3EAfgGQAAABAAAAAQBxAH4AlXNxAH4Bl3EAfgGmcQB+AJh4cQB+AJlxAH4Am3NxAH4Bl3EAfgGmcQB+AKp4cQB+AKt4c3EAfgAeAAAAAncEAAAAAnNyABRzcGVjLmN2bGFzdC5DVkxQYXJhbZUgQywsLU7ZAgAETAACaWRxAH4AF0wACm9yaWdpbmFsSWRxAH4AF0wABXJhbmdlcQB+AA9MAAR0eXBlcQB+AMB4cHEAfgAjcQB+ACNzcQB+AChzcQB+ACwAAAAhAAAAB3EAfgAuc3EAfgAsAAAAGwAAAAdxAH4Bk3NxAH4BunEAfgBXcQB+AFdzcQB+AChzcQB+ACwAAAA5AAAAB3EAfgAuc3EAfgAsAAAAIwAAAAdxAH4BlXhzcQB+AChzcQB+ACwAAAABAAAADHEAfgAuc3EAfgAsAAAAAAAAAAdzcgAkc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRWb2lki6Bk1Y34dWcCAAB4cQB+AZJxAH4AynQADENWTCBmdW5jdGlvbgAAAAl4c3EAfgAeAAAAAXcEAAAAAXNxAH4A1HEAfgCRc3EAfgDUcQB+AIBzcQB+ANdzcQB+ANRxAH4A2nNxAH4AIHEAfgDccQB+ANxxAH4A3XEAfgBUcQB+AOFxAH4A6HEAfgDzcQB+APdxAH4A+3hzcQB+AP8BAHBzcQB+AQJzcQB+ANRxAH4AkXNxAH4A1HEAfgCAc3EAfgDXc3EAfgDUcQB+ANpzcQB+ACBxAH4A3HEAfgDccQB+AQpxAH4AVHEAfgEOcQB+ARJxAH4BF3EAfgEbcQB+AR9zcQB+ASNzcQB+ACBxAH4AI3EAfgAjcQB+ASdxAH4AVHEAfgErcQB+ATJxAH4BNnEAfgE6cQB+AMpzcQB+AMNwcQB+AT5xAH4AynNxAH4AHgAAAAF3BAAAAAFzcQB+ANRxAH4AqnNxAH4A13NxAH4A1HEAfgDac3EAfgAgcQB+ANxxAH4A3HEAfgFGcQB+AFRxAH4BSnEAfgFOcQB+AVNxAH4BV3hzcQB+AP8BAHBzcQB+AQJzcQB+ANRxAH4AqnNxAH4A13NxAH4A1HEAfgDac3EAfgAgcQB+ANxxAH4A3HEAfgFhcQB+AFRxAH4BZXEAfgFpcQB+AW5xAH4BcnNxAH4BI3NxAH4AIHEAfgAjcQB+ACNxAH4BeHEAfgBUcQB+AXxxAH4Bg3EAfgGHcQB+AYtxAH4AynhxAH4AYnNxAH4AvHEAfgBic3EAfgAeAAAAAncEAAAAAnEAfgGTcQB+AZV4c3EAfgAeAAAAAncEAAAAAnEAfgG7cQB+Ab94cQB+AcNxAH4Bx3EAfgDKcQB+AchxAH4AZHEAfgAycQB+Acdwc3EAfgAeAAAAAncEAAAAAnEAfgBrcQB+AHR4cQB+AKxxAH4AMnEAfgCwcHNyABZzcGVjLkNWTCRFeHRlcm5hbEV4YWN05zCZO5TXQTgCAAJMAApzaWdoYXNoSW50dAAQTGV2bS9TaWdoYXNoSW50O0wACXNpZ25hdHVyZXQAL0xzcGVjL2N2bGFzdC9RdWFsaWZpZWRNZXRob2RQYXJhbWV0ZXJTaWduYXR1cmU7eHBzcgAOZXZtLlNpZ2hhc2hJbnQ9u2p6kPim1QIAAUwAAW5xAH4A5nhwc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAAEhwvzk3hzcgA3c3BlYy5jdmxhc3QuUXVhbGlmaWVkTWV0aG9kU2lnbmF0dXJlJFF1YWxpZmllZE1ldGhvZFNpZ1AXK1Dt5GJsAgADTAAGcGFyYW1zcQB+AA5MABNxdWFsaWZpZWRNZXRob2ROYW1ldAAoTHNwZWMvY3ZsYXN0L0NvbnRyYWN0RnVuY3Rpb25JZGVudGlmaWVyO0wAA3Jlc3EAfgAOeHBxAH4AZ3NyAB1zcGVjLmN2bGFzdC5RdWFsaWZpZWRGdW5jdGlvbuUpTPLkOVGDAgACTAAEaG9zdHQAHkxzcGVjL2N2bGFzdC9Tb2xpZGl0eUNvbnRyYWN0O0wACG1ldGhvZElkcQB+ABd4cHNyABxzcGVjLmN2bGFzdC5Tb2xpZGl0eUNvbnRyYWN0I2l9dxqBPaICAAFMAARuYW1lcQB+ABd4cHQADFRlc3RDb250cmFjdHQACHdvcmtPblMxcQB+AEBzcgATdmMuZGF0YS5DYWxsU3VtbWFyeUItIzxjYcyCAgARSQAJc3VtbWFyeUlkTAAOY2FsbENvbnZlbnRpb250ACZMaW5zdHJ1bWVudGF0aW9uL2NhbGxzL0NhbGxDb252ZW50aW9uO0wACmNhbGxUYXJnZXRxAH4ABUwACGNhbGxUeXBldAAVTHZjL2RhdGEvVEFDQ2FsbFR5cGU7TAAPY2Fubm90QmVJbmxpbmVkdAAtTGFuYWx5c2lzL2ljZmcvSW5saW5lciRJbGxlZ2FsSW5saW5pbmdSZWFzb247TAAGZ2FzVmFydAATTHZjL2RhdGEvVEFDU3ltYm9sO0wABmluQmFzZXQAF0x2Yy9kYXRhL1RBQ1N5bWJvbCRWYXI7TAAIaW5PZmZzZXRxAH4CAEwABmluU2l6ZXEAfgIATAAMb3JpZ0NhbGxjb3JldAAgTHZjL2RhdGEvVEFDQ21kJFNpbXBsZSRDYWxsQ29yZTtMAAdvdXRCYXNlcQB+AgFMAAlvdXRPZmZzZXRxAH4CAEwAB291dFNpemVxAH4CAEwADXNpZ1Jlc29sdXRpb25xAH4ABUwAFXN5bWJvbGljU2lnUmVzb2x1dGlvbnQAM0xhbmFseXNpcy9wdGEvYWJpL0RlY29kZXJBbmFseXNpcyRCdWZmZXJBY2Nlc3NQYXRoO0wABXRvVmFycQB+AgBMAAh2YWx1ZVZhcnEAfgIAeHAAAAAAc3IAJGluc3RydW1lbnRhdGlvbi5jYWxscy5DYWxsQ29udmVudGlvbn3WuJZoGBReAgADSQAIY2FsbGVySWRMAAVpbnB1dHQAGUxhbmFseXNpcy9pY2ZnL0NhbGxJbnB1dDtMAAZyYXdPdXR0ACJMaW5zdHJ1bWVudGF0aW9uL2NhbGxzL0NhbGxPdXRwdXQ7eHAAAAAAc3IAF2FuYWx5c2lzLmljZmcuQ2FsbElucHV0A/PbfbZhAnICAAdMAAdiYXNlVmFydAAZTHZjL2RhdGEvVEFDRXhwciRTeW0kVmFyO0wAEGVuY29kZWRBcmd1bWVudHN0ACNMYW5hbHlzaXMvaWNmZy9BQklBcmd1bWVudEVuY29kaW5nO0wAE2lucHV0U2l6ZUxvd2VyQm91bmRxAH4A5kwABm9mZnNldHQAFUx2Yy9kYXRhL1RBQ0V4cHIkU3ltO0wAFHJhbmdlVG9EZWNvbXBvc2VkQXJndAAPTGphdmEvdXRpbC9NYXA7TAAQc2ltcGxpZmllZE9mZnNldHQAG0x2Yy9kYXRhL1RBQ0V4cHIkU3ltJENvbnN0O0wABHNpemVxAH4CDHhwc3IAF3ZjLmRhdGEuVEFDRXhwciRTeW0kVmFyfe5noueTVdMCAAJMAAFzcQB+AgFMAAN0YWd0AAlMdGFjL1RhZzt4cgATdmMuZGF0YS5UQUNFeHByJFN5baJWPRLhhI1QAgAAeHIAD3ZjLmRhdGEuVEFDRXhwcgXagEbp4tB5AgAAeHBzcgA2dmMuZGF0YS5UQUNTeW1ib2wkVmFyJFdpdGhEZWZhdWx0Q2FsbEluZGV4JFdpdGhCeXRlTWFwlCRl91uHeScCAAJMAARtZXRhdAAeTGNvbS9jZXJ0b3JhL2NvbGxlY3QvVHJlYXBNYXA7TAAKbmFtZVByZWZpeHEAfgAXeHIAFXZjLmRhdGEuVEFDU3ltYm9sJFZhcvxIa9S+MEYRAgAAeHIAEXZjLmRhdGEuVEFDU3ltYm9sEpMi2OesctQCAAB4cHNyACBjb20uY2VydG9yYS5jb2xsZWN0Lkhhc2hUcmVhcE1hcM4n+3qupXKcAgADTAADa2V5cQB+ADRMAARuZXh0dAArTGNvbS9jZXJ0b3JhL2NvbGxlY3QvS2V5VmFsdWVQYWlyTGlzdCRNb3JlO0wABXZhbHVlcQB+ADR4cgAkY29tLmNlcnRvcmEuY29sbGVjdC5BYnN0cmFjdFRyZWFwTWFwLW7dR2hNBhkCAAB4cgAZY29tLmNlcnRvcmEuY29sbGVjdC5UcmVhcP/ew+O23D8jAgACTAAEbGVmdHQAG0xjb20vY2VydG9yYS9jb2xsZWN0L1RyZWFwO0wABXJpZ2h0cQB+Ah54cHBzcQB+Ahpwc3EAfgIacHBzcgALdGFjLk1ldGFLZXlq9heKQ7Ki3QIAA0wAD2VyYXN1cmVTdHJhdGVneXQAHUx0YWMvTWV0YUtleSRFcmFzdXJlU3RyYXRlZ3k7TAAEbmFtZXEAfgAXTAADdHlwdAARTGphdmEvbGFuZy9DbGFzczt4cH5yABt0YWMuTWV0YUtleSRFcmFzdXJlU3RyYXRlZ3kAAAAAAAAAABIAAHhxAH4AU3QACUNhbm9uaWNhbHQAFHRhYy5tZW1vcnkucGFydGl0aW9udnIAI2FuYWx5c2lzLnB0YS5hYmkuVW5pbmRleGVkUGFydGl0aW9uMMLWXmbWtIECAAFJAAJpZHhwcHNxAH4CKgAAAABzcQB+AiJxAH4CJ3QAElRhYy5zeW1ib2wua2V5d29yZHZyACJ2Yy5kYXRhLlRBQ1N5bWJvbCRWYXIkS2V5d29yZEVudHJ5TuPA5DR23HYCAAB4cHBzcgAydmMuZGF0YS5UQUNTeW1ib2wkVmFyJEtleXdvcmRFbnRyeSRUQUNLZXl3b3JkRW50cnm4mRaPLAQsrQIAAkkAFm1heWJlVEFDS2V5d29yZE9yZGluYWxMAARuYW1lcQB+ABd4cQB+Ai8AAAABdAAEdGFjTXNxAH4CInEAfgIndAANdGFjLmlzLm1lbW9yeXZyACJ0YWMuTWV0YU1hcCRDb21wYW5pb24kTm90aGluZ1ZhbHVlvuedFl+sVJACAAB4cHBzcQB+AjZ0AA90YWNNQ0FOT04wISExMjJzcgAPdGFjLlRhZyRCeXRlTWFwNb/Ry6GDRgkCAAB4cgALdGFjLlRhZyRNYXABJytzDV3P/QIAAHhyAAd0YWMuVGFneiXiZp1BxfUCAAB4cHBzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAICBHhzcQB+AhBzcgA1dmMuZGF0YS5UQUNTeW1ib2wkVmFyJFdpdGhEZWZhdWx0Q2FsbEluZGV4JFdpdGhCaXQyNTaereCTFyF7ZAIAAkwABG1ldGFxAH4CFkwACm5hbWVQcmVmaXhxAH4AF3hxAH4CF3NxAH4CGnNxAH4CGnBwcQB+Ai1wc3EAfgIxAAAALXQAAUxwc3EAfgIicQB+Aid0ABB0YWMuc3RhY2suaGVpZ2h0dnEAfgA2cHNxAH4ANgAAA/l0AARSMTIzc3IADnRhYy5UYWckQml0MjU2DCT7rQv8oqACAAB4cgAMdGFjLlRhZyRCaXRzjZYYd2kjC5gCAAZJAAhiaXR3aWR0aEwACW1heFNpZ25lZHEAfgDmTAALbWF4VW5zaWduZWRxAH4A5kwAC21pblNpZ25lZDJzcQB+AOZMAA1taW5TaWduZWRNYXRocQB+AOZMAAdtb2R1bHVzcQB+AOZ4cQB+AjwAAAEAc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAAgf/////////////////////////////////////////94c3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAAg//////////////////////////////////////////94c3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAAggAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4c3EAfgDp///////////////+/////v////91cQB+AOwAAAAggAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4c3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAAhAQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAeHNyACFkYXRhc3RydWN0dXJlcy5MaW5rZWRBcnJheUhhc2hNYXAAAAAAAAAAAQMAAkYACmxvYWRGYWN0b3JMAAloYXNoVGFibGV0AC5MZGF0YXN0cnVjdHVyZXMvYXJyYXloYXNodGFibGUvQXJyYXlIYXNoVGFibGU7eHB3CAAAABFAAAAAc3IAHmFuYWx5c2lzLmljZmcuU2NyYXRjaEJ5dGVSYW5nZXAVSDd1wqZEAgACTAAEZnJvbXEAfgDmTAACdG9xAH4A5nhwcQB+AOtxAH4BLHNyAC1hbmFseXNpcy5pY2ZnLkRlY29tcG9zZWRDYWxsSW5wdXRBcmckQ29uc3RhbnRfXwzYyd/Y1QIAA0wAAWN0ABlMdmMvZGF0YS9UQUNTeW1ib2wkQ29uc3Q7TAARY29udHJhY3RSZWZlcmVuY2V0AC9MYW5hbHlzaXMvaWNmZy9DYWxsR3JhcGhCdWlsZGVyJENhbGxlZENvbnRyYWN0O0wADHNjcmF0Y2hSYW5nZXQAIExhbmFseXNpcy9pY2ZnL1NjcmF0Y2hCeXRlUmFuZ2U7eHIAJGFuYWx5c2lzLmljZmcuRGVjb21wb3NlZENhbGxJbnB1dEFyZ4FzEw1US8lhAgAAeHBzcgAXdmMuZGF0YS5UQUNTeW1ib2wkQ29uc3TG9EmaKpZ8oQIAAkwAA3RhZ3EAfgIRTAAFdmFsdWVxAH4A5nhxAH4CGHEAfgJOc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAAghwvzkwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB4cHEAfgJdc3EAfgJcc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAABBHhzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAEjeHNyAC1hbmFseXNpcy5pY2ZnLkRlY29tcG9zZWRDYWxsSW5wdXRBcmckVmFyaWFibGVIk8OZCF22TgIAA0wAEWNvbnRyYWN0UmVmZXJlbmNlcQB+AmBMAAxzY3JhdGNoUmFuZ2VxAH4CYUwAAXZxAH4CAXhxAH4CYnNyADthbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ2FsbGVkQ29udHJhY3QkU3ltYm9saWNJbnB1dNyKJAiCH3KFAgACTAAIaW5wdXRBcmdxAH4CAUwABm9mZnNldHEAfgDmeHIALWFuYWx5c2lzLmljZmcuQ2FsbEdyYXBoQnVpbGRlciRDYWxsZWRDb250cmFjdNMLdazfy6HXAgAAeHBzcQB+AkFzcQB+AhpzcQB+AhpzcQB+AhpwcHNxAH4CInEAfgIndAATdGFjLmltbXV0YWJsZS5hcnJheXZyABZ2Yy5kYXRhLkltbXV0YWJsZUJvdW5k6BxyxCddyJ8CAAFMAANzeW1xAH4CAHhwcHNxAH4CeHNxAH4CQXNxAH4CGnBwcQB+Ai1wc3EAfgIxAAAADHQAD3RhY0NhbGxkYXRhc2l6ZXEAfgJ+c3EAfgIac3EAfgIacHBzcQB+AiJxAH4CJ3QAD3RhYy53b3JkbWFwLWtleXZxAH4A6XBxAH4CaXBzcQB+AiJxAH4CJ3QAFnRhYy5zY2FsYXJpemF0aW9uLnNvcnR2cgAZdmMuZGF0YS5TY2FsYXJpemF0aW9uU29ydFZidQ24nhXJAgAAeHBwc3IAH3ZjLmRhdGEuU2NhbGFyaXphdGlvblNvcnQkU3BsaXSnfUjNXsad9QIAAUwAA2lkeHEAfgDmeHEAfgKGcQB+AmlxAH4CLXBzcQB+AjEAAAAPdAAOdGFjQ2FsbGRhdGFidWZzcQB+Ahpwc3EAfgIacHBzcQB+AiJxAH4CJ3QAD3RhYy5pcy5jYWxsZGF0YXEAfgI3cHEAfgI4c3EAfgIicQB+Aid0ABN0YWMuY2FsbGRhdGEub2Zmc2V0cQB+AoNwcQB+AmlzcQB+AiJxAH4CJ3QAFXRhYy5zdG9yYWdlLmJpdC13aWR0aHEAfgJJcHNxAH4ANgAAAQB0ABB0YWNDYWxsZGF0YWJ1ZiE0cQB+AmlxAH4CaHNxAH4CQXNxAH4CGnBwc3EAfgIicQB+Aid0ABh0YWMuZGVjb21wLWluc2NhbGFyLnNvcnR2cgAddGFjLkRlY29tcG9zZWRJbnB1dFNjYWxhclNvcnQmAfs4+h6eTwIAAHhwcHNyACR0YWMuRGVjb21wb3NlZElucHV0U2NhbGFyU29ydCRTaW1wbGWldTOROGCA+AIAAUwACmJ5dGVPZmZzZXRxAH4A5nhxAH4CmnEAfgJpdAADUjU2c3EAfgJcc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAABJHhzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAFDeHNxAH4CbXNyADxhbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ2FsbGVkQ29udHJhY3QkVW5yZXNvbHZlZFJlYWS1p9/nIAGtXwIAAUkADXN0b3JhZ2VSZWFkSWR4cQB+AnAAAAAAcQB+Ap9zcQB+AkFzcQB+AhpzcQB+Ahpwc3EAfgIacHBxAH4CLXBxAH4CRXEAfgKYcHNxAH4CnHEAfgKgcHEAfgJHcHNxAH4ANgAAA+t0AANSNTlzcQB+AlxzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAFEeHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAWN4c3EAfgJtc3EAfgKlAAAAAXEAfgKuc3EAfgJBc3EAfgIac3EAfgIacHNxAH4CGnBwcQB+Ai1wcQB+AkVxAH4CmHBzcQB+ApxxAH4Cr3BxAH4CR3BxAH4CrHQAA1I2M3NxAH4CXHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAWR4c3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAABg3hzcQB+Am1wcQB+ArtzcQB+AkFzcQB+AhpzcQB+Ahpwc3EAfgIacHBxAH4CLXBxAH4CRXEAfgKYcHNxAH4CnHEAfgK8cHEAfgJHcHEAfgKsdAADUjY0c3EAfgJcc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAABhHhzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAGjeHNxAH4CbXBxAH4Cx3NxAH4CQXNxAH4CGnNxAH4CGnBzcQB+AhpwcHEAfgItcHEAfgJFcQB+Aphwc3EAfgKccQB+AshwcQB+AkdwcQB+Aqx0AANSNjVzcQB+AlxzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAGkeHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAcN4c3EAfgJtcHEAfgLTc3EAfgJBc3EAfgIac3EAfgIacHNxAH4CGnBwcQB+Ai1wcQB+AkVxAH4CmHBzcQB+ApxxAH4C1HBxAH4CR3BzcQB+ADYAAAPkdAADUjc0c3EAfgJcc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAABxHhzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAHjeHNxAH4CbXNxAH4CpQAAAAJxAH4C4HNxAH4CQXNxAH4CGnNxAH4CGnBzcQB+AhpwcHEAfgItcHEAfgJFcQB+Aphwc3EAfgKccQB+AuFwcQB+AkdwcQB+Aqx0AANSNzhzcQB+AlxzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAHkeHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAgEDeHNxAH4CbXBxAH4C7XNxAH4CQXNxAH4CGnNxAH4CGnBzcQB+AhpwcHEAfgItcHEAfgJFcQB+Aphwc3EAfgKccQB+Au5wcQB+AkdwcQB+At50AANSODRzcQB+AlxzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAIBBHhzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAIBI3hzcQB+Am1zcQB+AqUAAAADcQB+AvlzcQB+AkFzcQB+AhpzcQB+Ahpwc3EAfgIacHBxAH4CLXBxAH4CRXEAfgKYcHNxAH4CnHEAfgL6cHEAfgJHcHEAfgKsdAADUjg5c3EAfgJcc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAACASR4c3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAACAUN4c3EAfgJtc3EAfgKlAAAABHEAfgMGc3EAfgJBc3EAfgIac3EAfgIacHNxAH4CGnBwcQB+Ai1wcQB+AkVxAH4CmHBzcQB+ApxxAH4DB3BxAH4CR3BxAH4CrHQAA1I5M3NxAH4CXHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAgFEeHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAgFjeHNxAH4CbXBxAH4DE3NxAH4CQXNxAH4CGnNxAH4CGnBzcQB+AhpwcHEAfgItcHEAfgJFcQB+Aphwc3EAfgKccQB+AxRwcQB+AkdwcQB+Aqx0AANSOTRzcQB+AlxzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAIBZHhzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAIBg3hzcQB+Am1wcQB+Ax9zcQB+AkFzcQB+AhpzcQB+Ahpwc3EAfgIacHBxAH4CLXBxAH4CRXEAfgKYcHNxAH4CnHEAfgMgcHEAfgJHcHEAfgKsdAADUjk1c3EAfgJcc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAACAYR4c3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAACAaN4c3EAfgJtcHEAfgMrc3EAfgJBc3EAfgIac3EAfgIacHNxAH4CGnBwcQB+Ai1wcQB+AkVxAH4CmHBzcQB+ApxxAH4DLHBxAH4CR3BxAH4C3nQABFIxMDRzcQB+AlxzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAIBpHhzcQB+AOn///////////////7////+AAAAAXVxAH4A7AAAAAIBw3hzcQB+Am1zcQB+AqUAAAAFcQB+AzdzcQB+AkFzcQB+AhpzcQB+Ahpwc3EAfgIacHBxAH4CLXBxAH4CRXEAfgKYcHNxAH4CnHEAfgM4cHEAfgJHcHEAfgKsdAAEUjEwOHNxAH4CXHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAgHEeHNxAH4A6f///////////////v////4AAAABdXEAfgDsAAAAAgHjeHNxAH4CbXBxAH4DRHNxAH4CQXNxAH4CGnNxAH4CGnBzcQB+AhpwcHEAfgItcHEAfgJFcQB+Aphwc3EAfgKccQB+A0VwcQB+AkdwcQB+At50AARSMTE0c3EAfgJcc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAACAeR4c3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAACAgN4c3EAfgJtcHEAfgNQc3EAfgJBc3EAfgIac3EAfgIacHNxAH4CGnBwcQB+Ai1wcQB+AkVxAH4CmHBzcQB+ApxxAH4DUXBxAH4CR3BzcQB+ADYAAAPqdAAEUjEyMHhwc3EAfgIQc3EAfgJBc3EAfgIac3EAfgIacHBxAH4CLXBxAH4CRXBxAH4CR3BzcQB+ADYAAAP4dAAEUjEyNHEAfgJOc3IAIGluc3RydW1lbnRhdGlvbi5jYWxscy5DYWxsT3V0cHV0GMeJA1KhvckCAANMAARiYXNlcQB+AgFMAAZvZmZzZXRxAH4CAEwABHNpemVxAH4CAHhwc3EAfgIVc3EAfgIacHNxAH4CGnBzcQB+AhpwcHEAfgIlcHNxAH4CKgAAAAJxAH4CLXBxAH4CMnEAfgI0cHEAfgI4dAANdGFjTUNBTk9OMSEhNnNxAH4CQXNxAH4CGnNxAH4CGnBwcQB+Ai1wcQB+AkVwcQB+AkdwcQB+AkpxAH4CS3NxAH4CZHEAfgJOcQB+AOtzcgAhZGF0YXN0cnVjdHVyZXMuTGlua2VkQXJyYXlIYXNoU2V0AAAAAAAAAAEDAAJGAApsb2FkRmFjdG9yTAAJaGFzaFRhYmxlcQB+Alp4cHcIAAAAAUAAAABzcgBEYW5hbHlzaXMuaWNmZy5DYWxsR3JhcGhCdWlsZGVyJENhbGxlZENvbnRyYWN0JEZ1bGx5UmVzb2x2ZWQkU2VsZkxpbmt9Z6nxMSg7UgIAAUwACmNvbnRyYWN0SWRxAH4A5nhyADthbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ2FsbGVkQ29udHJhY3QkRnVsbHlSZXNvbHZlZO7+cDEhb6htAgAAeHEAfgJwc3EAfgDp///////////////+/////gAAAAF1cQB+AOwAAAAQzkYEoAAAAAAAAAAAAAAAAXh4fnIAE3ZjLmRhdGEuVEFDQ2FsbFR5cGUAAAAAAAAAABIAAHhxAH4AU3QADFJFR1VMQVJfQ0FMTHBzcQB+AkFzcQB+AhpzcQB+AhpwcHEAfgItcHEAfgJFcHEAfgJHcHNxAH4ANgAAA/R0AARSMTI2c3EAfgIVc3EAfgIacHNxAH4CGnBzcQB+AhpwcHEAfgIlcHEAfgIscQB+Ai1wcQB+AjJxAH4CNHBxAH4COHEAfgI5c3EAfgJBcQB+AkNxAH4CS3NxAH4CZHEAfgJOcQB+Aj5zcgAedmMuZGF0YS5UQUNDbWQkU2ltcGxlJENhbGxDb3JlJWSzvKU57xkCAAtMAAhjYWxsVHlwZXEAfgH+TAADZ2FzcQB+AgBMAAZpbkJhc2VxAH4CAUwACGluT2Zmc2V0cQB+AgBMAAZpblNpemVxAH4CAEwABG1ldGFxAH4CFkwAB291dEJhc2VxAH4CAUwACW91dE9mZnNldHEAfgIATAAHb3V0U2l6ZXEAfgIATAACdG9xAH4CAEwABXZhbHVlcQB+AgB4cgAVdmMuZGF0YS5UQUNDbWQkU2ltcGxlT0Nt+Addc6ECAAB4cgATdmMuZGF0YS5UQUNDbWQkU3BlY3wzENS6oQbcAgAAeHIADnZjLmRhdGEuVEFDQ21k0holn/1bo/sCAAB4cHEAfgN3c3EAfgJBcQB+A3pxAH4DfXNxAH4CFXNxAH4CGnBzcQB+Ahpwc3EAfgIacHBxAH4CJXBxAH4CLHEAfgItcHEAfgIycQB+AjRwcQB+AjhxAH4COXNxAH4CQXEAfgJDcQB+AktzcQB+AkFxAH4DX3EAfgNic3EAfgIacHBzcQB+AiJ+cQB+AiZ0AAlDYWxsVHJhY2V0AAh0YWMubWV0YXZyABN2Yy5kYXRhLlRBQ01ldGFJbmZvRbtRIq0KVdsCAAZJAAViZWdpbkkAA2xlbkkABnNvdXJjZUwAB2FkZHJlc3NxAH4A5kwACGp1bXBUeXBldAATTGNvbXBpbGVyL0p1bXBUeXBlO0wADXNvdXJjZUNvbnRleHR0ABhMY29tcGlsZXIvU291cmNlQ29udGV4dDt4cHBzcQB+A5UAAAFvAAAAFgAAAABxAH4DdH5yABFjb21waWxlci5KdW1wVHlwZQAAAAAAAAAAEgAAeHEAfgBTdAAHUkVHVUxBUnNyABZjb21waWxlci5Tb3VyY2VDb250ZXh0g3i13hFi1ssCAAJMAA9pbmRleFRvRmlsZVBhdGhxAH4CDUwACXNvdXJjZURpcnEAfgAXeHBzcQB+All3CAAAAAFAAAAAc3EAfgA2AAAAAHQAEFRlc3RDb250cmFjdC5zb2x4dAATLnBvc3RfYXV0b2ZpbmRlcnMuMHNxAH4CFXNxAH4CGnBzcQB+Ahpwc3EAfgIacHBxAH4CJXBzcQB+AioAAAACcQB+Ai1wcQB+AjJxAH4CNHBxAH4COHEAfgNqc3EAfgJBcQB+A2xxAH4CS3EAfgNuc3EAfgJBc3EAfgIac3EAfgIac3EAfgIacHNxAH4CGnBwc3EAfgIifnEAfgImdAAGRXJhc2VkdAAadGFjLmNvbnRyYWN0LnN5bS5hZGRyLm5hbWV2cgAQamF2YS5sYW5nLlN0cmluZ6DwpDh6O7NCAgAAeHBwcQB+AfpxAH4CLXBxAH4CRXBzcQB+AiJxAH4Dr3QAFXRhYy5jb250cmFjdC5zeW0uYWRkcnEAfgKDcHEAfgN0cHEAfgJHcHNxAH4ANgAAA/10AANSMjhzcQB+AmRxAH4CTnEAfgDrc3EAfgIVc3EAfgIacHNxAH4CGnBzcQB+AhpwcHEAfgIlcHNxAH4CKgAAAAJxAH4CLXBxAH4CMnEAfgI0cHEAfgI4cQB+A2pzcQB+AkFxAH4DbHEAfgJLcQB+A25zcgAiamF2YS51dGlsLkNvbGxlY3Rpb25zJFNpbmdsZXRvblNldCxSQZgpwLG/AgABTAAHZWxlbWVudHEAfgA0eHBxAH4B8HBzcQB+AkFzcQB+AhpzcQB+AhpzcQB+Ahpwc3EAfgIacHBxAH4DrnBxAH4B+nEAfgItcHEAfgJFcHEAfgO0cHEAfgN0cHEAfgJHcHEAfgO2cQB+A7dzcQB+AmRxAH4CTnEAfgDrc3IAQHJlcG9ydC5jYWxscmVzb2x1dGlvbi5DYWxsUmVzb2x1dGlvblRhYmxlU3VtbWFyeUluZm8kRGVmYXVsdEluZm/dcr/wlck5tQIAAUwAEWFwcGxpY2F0aW9uUmVhc29udAAoTGFuYWx5c2lzL2ljZmcvU3VtbWFyeUFwcGxpY2F0aW9uUmVhc29uO3hyADRyZXBvcnQuY2FsbHJlc29sdXRpb24uQ2FsbFJlc29sdXRpb25UYWJsZVN1bW1hcnlJbmZvGrbQRtpmzIYCAAFMAA1pbmZvJGRlbGVnYXRlcQB+ADF4cHNxAH4AM3NxAH4CWXcIAAAAAUAAAAB0ABpzdW1tYXJ5IGFwcGxpY2F0aW9uIHJlYXNvbnQAPmRlY2xhcmVkIGF0IHRlc3Quc3BlYzo0OjY3IHRvIGFwcGx5IHRvIGFsbCBjYWxscyB0byB0aGUgY2FsbGVleHNyAC9hbmFseXNpcy5pY2ZnLlN1bW1hcnlBcHBsaWNhdGlvblJlYXNvbiRTcGVjJEFsbDVbfdlUEwDtAgACTAADbG9jcQB+AA9MAA9tZXRob2RTaWduYXR1cmVxAH4AF3hyACthbmFseXNpcy5pY2ZnLlN1bW1hcnlBcHBsaWNhdGlvblJlYXNvbiRTcGVjnk8P0pteLB0CAAB4cgAmYW5hbHlzaXMuaWNmZy5TdW1tYXJ5QXBwbGljYXRpb25SZWFzb25CnD+iq+g4mgIAAHhwcQB+AKx0ACd3b3JrT25TMSh1aW50MjU2LCBUZXN0Q29udHJhY3QuQ29tcGxleClxAH4DmXNyACBjb20uY2VydG9yYS5jb2xsZWN0Lkhhc2hUcmVhcFNldI5hR0C7LF30AgACTAAHZWxlbWVudHEAfgA0TAAEbmV4dHQAJkxjb20vY2VydG9yYS9jb2xsZWN0L0VsZW1lbnRMaXN0JE1vcmU7eHIAJGNvbS5jZXJ0b3JhLmNvbGxlY3QuQWJzdHJhY3RUcmVhcFNldKmhUoCW3/t2AgAAeHEAfgIdc3EAfgPUc3EAfgPUcHNxAH4D1HNxAH4D1HNxAH4D1HBwcQB+A8Fwc3EAfgPUcHBxAH4Cp3BxAH4ClnBzcQB+A9RzcQB+A9RzcQB+A9RwcHEAfgLBcHBxAH4CzXBzcQB+A9Rwc3EAfgPUcHNxAH4D1HBwcQB+AwBwcQB+AvNwcQB+AudwcQB+AtlwcQB+ArVwcQB+A7lwcHEAfgMNcHNxAH4D1HNxAH4D1HBzcQB+A9RzcQB+A9RwcHEAfgMxcHBxAH4DPnBxAH4DJXBzcQB+A9RzcQB+A9RzcQB+A9RzcQB+A9RwcHEAfgNWcHBxAH4CQnBzcQB+A9RwcHEAfgN5cHEAfgNecHBxAH4CGXBxAH4DSnBxAH4DGXA="}
		AssignExpCmd calledContract:17 R28:117
		AssignExpCmd executingContract:109 R28:117
		AssignExpCmd CANON2!!128:10 R28:117
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLFunctionStart","callIndex":3,"name":"workOnSComplexCVL","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":3,"charByteOffset":66},"end":{"line":3,"charByteOffset":89}},"isNoRevert":true}}
		LabelCmd "72: Move primitive value for variable x15771578:int..."
		LabelCmd "...done 72"
		AssignExpCmd CANON66:85 tacCalldatabufCANON0@1:179
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLArg.PrimitiveArg","callIndex":3,"index":0,"sym":{"namePrefix":"CANON66","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":27},"end":{"line":7,"charByteOffset":33}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"x"}]},"param":{"Named_type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"id":"x","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":27},"end":{"line":7,"charByteOffset":33}}}}}
		LabelCmd "144: Write struct..."
		LabelCmd "108: Write field s1 for variable s15791580:TestContract.Complex..."
		LabelCmd "107: Write struct..."
		LabelCmd "77: Write field x for variable tacTmp!fields11996:TestContract.Simple..."
		LabelCmd "76: Move primitive value for variable tacTmp!fieldx2001:int..."
		LabelCmd "...done 76"
		LabelCmd "...done 77"
		LabelCmd "80: Write field y for variable tacTmp!fields11996:TestContract.Simple..."
		LabelCmd "78: Move primitive value for variable tacTmp!fieldy2007:int..."
		LabelCmd "...done 78"
		LabelCmd "...done 80"
		LabelCmd "83: Write field z1 for variable tacTmp!fields11996:TestContract.Simple..."
		LabelCmd "82: Move primitive value for variable tacTmp!fieldz12020:int..."
		LabelCmd "...done 82"
		LabelCmd "...done 83"
		LabelCmd "86: Write field z2 for variable tacTmp!fields11996:TestContract.Simple..."
		LabelCmd "84: Move primitive value for variable tacTmp!fieldz22025:int..."
		LabelCmd "...done 84"
		LabelCmd "...done 86"
		LabelCmd "97: Write field b1 for variable tacTmp!fields11996:TestContract.Simple..."
		LabelCmd "96: Move primitive value for variable tacTmp!fieldb12030:bool..."
		LabelCmd "...done 96"
		LabelCmd "...done 97"
		LabelCmd "99: Write field x2 for variable tacTmp!fields11996:TestContract.Simple..."
		LabelCmd "98: Move primitive value for variable tacTmp!fieldx22068:int..."
		LabelCmd "...done 98"
		LabelCmd "...done 99"
		LabelCmd "101: Write field b2 for variable tacTmp!fields11996:TestContract.Simple..."
		LabelCmd "100: Move primitive value for variable tacTmp!fieldb22073:bool..."
		LabelCmd "...done 100"
		LabelCmd "...done 101"
		LabelCmd "...done 107"
		LabelCmd "...done 108"
		LabelCmd "141: Write field s2 for variable s15791580:TestContract.Complex..."
		LabelCmd "140: Write struct..."
		LabelCmd "110: Write field x for variable tacTmp!fields22091:TestContract.Simple..."
		LabelCmd "109: Move primitive value for variable tacTmp!fieldx2096:int..."
		LabelCmd "...done 109"
		LabelCmd "...done 110"
		LabelCmd "112: Write field y for variable tacTmp!fields22091:TestContract.Simple..."
		LabelCmd "111: Move primitive value for variable tacTmp!fieldy2101:int..."
		LabelCmd "...done 111"
		LabelCmd "...done 112"
		LabelCmd "123: Write field z1 for variable tacTmp!fields22091:TestContract.Simple..."
		LabelCmd "113: Move primitive value for variable tacTmp!fieldz12106:int..."
		LabelCmd "...done 113"
		LabelCmd "...done 123"
		LabelCmd "125: Write field z2 for variable tacTmp!fields22091:TestContract.Simple..."
		LabelCmd "124: Move primitive value for variable tacTmp!fieldz22145:int..."
		LabelCmd "...done 124"
		LabelCmd "...done 125"
		LabelCmd "127: Write field b1 for variable tacTmp!fields22091:TestContract.Simple..."
		LabelCmd "126: Move primitive value for variable tacTmp!fieldb12150:bool..."
		LabelCmd "...done 126"
		LabelCmd "...done 127"
		LabelCmd "129: Write field x2 for variable tacTmp!fields22091:TestContract.Simple..."
		LabelCmd "128: Move primitive value for variable tacTmp!fieldx22159:int..."
		LabelCmd "...done 128"
		LabelCmd "...done 129"
		LabelCmd "131: Write field b2 for variable tacTmp!fields22091:TestContract.Simple..."
		LabelCmd "130: Move primitive value for variable tacTmp!fieldb22164:bool..."
		LabelCmd "...done 130"
		LabelCmd "...done 131"
		LabelCmd "...done 140"
		LabelCmd "...done 141"
		LabelCmd "143: Write field b3 for variable s15791580:TestContract.Complex..."
		LabelCmd "142: Move primitive value for variable tacTmp!fieldb32187:bool..."
		LabelCmd "...done 142"
		LabelCmd "...done 143"
		LabelCmd "...done 144"
		AnnotationCmd JSON{"key":{"name":"cvl.trace.data.movement","type":"spec.CVLCompiler$Companion$TraceMeta$CVLMovement","erasureStrategy":"Erased"},"value":{"dst":{"id":"s1576"},"src":{"id":"s15791580"}}}
		AssignExpCmd CANON77:86 R59:48
		AssignExpCmd CANON78:87 R63:48
		AssignExpCmd CANON79:88 R64:48
		AssignExpCmd CANON80:89 R65:48
		AssignExpCmd CANON81:90 LNot(Eq(R74:39 0x0 ) )
		AssignExpCmd CANON82:91 R78:48
		AssignExpCmd CANON83:92 LNot(Eq(R84:39 0x0 ) )
		AssignExpCmd CANON84:93 R89:48
		AssignExpCmd CANON85:94 R93:48
		AssignExpCmd CANON86:95 R94:48
		AssignExpCmd CANON87:96 R95:48
		AssignExpCmd CANON88:97 LNot(Eq(R104:39 0x0 ) )
		AssignExpCmd CANON89:98 R108:48
		AssignExpCmd CANON90:99 LNot(Eq(R114:39 0x0 ) )
		AssignExpCmd CANON91:100 LNot(Eq(R120:60 0x0 ) )
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLArg.StructArg","callIndex":3,"index":1,"symbols":[{"namePrefix":"CANON77","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s1.x"}]},{"namePrefix":"CANON78","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s1.y"}]},{"namePrefix":"CANON79","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s1.z1"}]},{"namePrefix":"CANON80","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s1.z2"}]},{"namePrefix":"CANON81","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s1.b1"}]},{"namePrefix":"CANON82","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s1.x2"}]},{"namePrefix":"CANON83","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s1.b2"}]},{"namePrefix":"CANON84","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s2.x"}]},{"namePrefix":"CANON85","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s2.y"}]},{"namePrefix":"CANON86","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s2.z1"}]},{"namePrefix":"CANON87","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s2.z2"}]},{"namePrefix":"CANON88","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s2.b1"}]},{"namePrefix":"CANON89","tag":{"#class":"tac.Tag.Int"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s2.x2"}]},{"namePrefix":"CANON90","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.s2.b2"}]},{"namePrefix":"CANON91","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.struct.path","type":"spec.cvlast.CVLStructPathNode","erasureStrategy":"CallTrace"},"value":{"rootStructType":{"name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"fields":[{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Function","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"s.b3"}]}],"param":{"Named_type":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Complex","fields":[{"fieldName":"s1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"s2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Struct","name":"TestContract.Simple","fields":[{"fieldName":"x","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"y","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"}},{"fieldName":"z1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"z2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":8}},{"fieldName":"b1","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}},{"fieldName":"x2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256}},{"fieldName":"b2","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]}},{"fieldName":"b3","cvlType":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"id":"s","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":7,"charByteOffset":35},"end":{"line":7,"charByteOffset":57}}}}}
		AnnotationCmd:180 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Havoc","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":8,"charByteOffset":4},"end":{"line":8,"charByteOffset":34}},"targets":[{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.ArrayDerefExp","array":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"testContract","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract","name":{"name":"TestContract"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":8,"charByteOffset":10},"end":{"line":8,"charByteOffset":22}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId","instanceId":"ce4604a0000000000000000000000001"}},"twoStateIndex":"NEITHER"},"fieldName":"m","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor","keyType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"valueType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"location":null},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":8,"charByteOffset":10},"end":{"line":8,"charByteOffset":24}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"index":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"0","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"0"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":8,"charByteOffset":25},"end":{"line":8,"charByteOffset":26}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":8,"charByteOffset":10},"end":{"line":8,"charByteOffset":27}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"fieldName":"s1","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":8,"charByteOffset":10},"end":{"line":8,"charByteOffset":30}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"fieldName":"b1","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":8,"charByteOffset":10},"end":{"line":8,"charByteOffset":33}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}}],"assumingExp":null,"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:181 I139:26 0x0
		AssertCmd:182 true "sanity bounds check on cvl to vm encoding failed (unsigned int elements of a user array)"
		AssignExpCmd:182 R140:21 Apply(hash_3_keccak:bif Apply(skey_basic:bif 0x40) Apply(skey_basic:bif 0x0) Apply(skey_basic:bif 0x0))
		AssignExpCmd:182 R141:21 Apply(skey_add:bif R140:21 0x1)
		AssignHavocCmd:182 B142:21
		AssignExpCmd:182 R143:21 Ite(B142:21 0x1 0x0 )
		AssignExpCmd:183 CANON41!!144:14 AnnotationExp(Store(CANON41!!14:14 R141:184 R143:21 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Const","value":"0"},"hashResult":{"#class":"vc.data.TACSymbol.Const","value":"0"}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"36"}}]}})
		AnnotationCmd:182 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.DirectStorageHavoc","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R143","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b1","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"test.spec","start":{"line":8,"charByteOffset":10},"end":{"line":8,"charByteOffset":33}}}}
		AssignExpCmd:185 B145:22 true
		AnnotationCmd:182 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":21}
		AnnotationCmd:186 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.AssumeCmd.Assume","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":4},"end":{"line":9,"charByteOffset":47}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.EqExp","l":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.ArrayDerefExp","array":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"testContract","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract","name":{"name":"TestContract"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":12},"end":{"line":9,"charByteOffset":24}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId","instanceId":"ce4604a0000000000000000000000001"}},"twoStateIndex":"NEITHER"},"fieldName":"m","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor","keyType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"valueType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"location":null},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":12},"end":{"line":9,"charByteOffset":26}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"index":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"0","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"0"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":27},"end":{"line":9,"charByteOffset":28}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":12},"end":{"line":9,"charByteOffset":29}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"fieldName":"s1","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":12},"end":{"line":9,"charByteOffset":32}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"fieldName":"b1","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":12},"end":{"line":9,"charByteOffset":35}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"r":{"#class":"spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"x","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":40},"end":{"line":9,"charByteOffset":41}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"3","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"3"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":44},"end":{"line":9,"charByteOffset":45}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":40},"end":{"line":9,"charByteOffset":45}},"hasParens":true}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":9,"charByteOffset":12},"end":{"line":9,"charByteOffset":46}}}},"description":null,"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"comesFromSpec":true}}}
		AssignExpCmd:187 I146:26 0x0
		AssertCmd:188 true "sanity bounds check on cvl to vm encoding failed (unsigned int elements of a user array)"
		AssignExpCmd:188 R147:21 Apply(hash_3_keccak:bif Apply(skey_basic:bif 0x40) Apply(skey_basic:bif 0x0) Apply(skey_basic:bif 0x0))
		AssignExpCmd:188 R148:21 Apply(skey_add:bif R147:21 0x1)
		AssignExpCmd:189 R149:21 AnnotationExp(Select(CANON41!!144:190 R148:191 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Const","value":"0"},"hashResult":{"#class":"vc.data.TACSymbol.Const","value":"0"}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"36"}}]}})
		AssumeExpCmd Eq(R149:21 0x0 )
		AssignExpCmd:188 B150:22 false
		AnnotationCmd:188 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.DirectStorageLoad","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"B150","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b1","base":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"s1","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"test.spec","start":{"line":9,"charByteOffset":12},"end":{"line":9,"charByteOffset":35}}}}
		AssignExpCmd:192 I151:23 CANON66:85
		AssignExpCmd:193 I152:24 0x3
		AssignExpCmd:194 B153:22 false
		AssignExpCmd:195 CANON106:25 true
		AnnotationCmd:188 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":22}
		AnnotationCmd:196 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Havoc","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":10,"charByteOffset":4},"end":{"line":10,"charByteOffset":31}},"targets":[{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.ArrayDerefExp","array":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"testContract","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract","name":{"name":"TestContract"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":10,"charByteOffset":10},"end":{"line":10,"charByteOffset":22}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId","instanceId":"ce4604a0000000000000000000000001"}},"twoStateIndex":"NEITHER"},"fieldName":"m","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor","keyType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"valueType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"location":null},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":10,"charByteOffset":10},"end":{"line":10,"charByteOffset":24}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"index":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"0","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"0"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":10,"charByteOffset":25},"end":{"line":10,"charByteOffset":26}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":10,"charByteOffset":10},"end":{"line":10,"charByteOffset":27}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"fieldName":"b3","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":10,"charByteOffset":10},"end":{"line":10,"charByteOffset":30}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}}],"assumingExp":null,"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:197 I154:26 0x0
		AssertCmd:198 true "sanity bounds check on cvl to vm encoding failed (unsigned int elements of a user array)"
		AssignExpCmd:198 R155:21 Apply(hash_3_keccak:bif Apply(skey_basic:bif 0x40) Apply(skey_basic:bif 0x0) Apply(skey_basic:bif 0x0))
		AssignExpCmd:198 R156:21 Apply(skey_add:bif R155:21 0x8)
		AssignHavocCmd:198 B157:21
		AssignExpCmd:198 R158:21 Ite(B157:21 0x1 0x0 )
		AssignExpCmd:199 CANON64!!159:84 AnnotationExp(Store(CANON64!!24:84 R156:200 R158:21 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Const","value":"0"},"hashResult":{"#class":"vc.data.TACSymbol.Const","value":"0"}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"100"}}]}})
		AnnotationCmd:198 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.DirectStorageHavoc","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"R158","tag":{"#class":"tac.Tag.Bit256"},"callIndex":0,"meta":[{"key":{"name":"tac.is-temp-var","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b3","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"test.spec","start":{"line":10,"charByteOffset":10},"end":{"line":10,"charByteOffset":30}}}}
		AssignExpCmd:201 B160:22 true
		AnnotationCmd:198 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":23}
		AnnotationCmd:202 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.AssumeCmd.Assume","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":4},"end":{"line":11,"charByteOffset":44}},"exp":{"#class":"spec.cvlast.CVLExp.RelopExp.EqExp","l":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.ArrayDerefExp","array":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"testContract","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract","name":{"name":"TestContract"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":12},"end":{"line":11,"charByteOffset":24}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId","instanceId":"ce4604a0000000000000000000000001"}},"twoStateIndex":"NEITHER"},"fieldName":"m","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor","keyType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"valueType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"location":null},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":12},"end":{"line":11,"charByteOffset":26}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"index":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"0","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"0"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":27},"end":{"line":11,"charByteOffset":28}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":12},"end":{"line":11,"charByteOffset":29}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"fieldName":"b3","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":12},"end":{"line":11,"charByteOffset":32}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"r":{"#class":"spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp","l":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"x","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.UIntK","k":256},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":37},"end":{"line":11,"charByteOffset":38}}},"twoStateIndex":"NEITHER"},"r":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"5","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"5"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":41},"end":{"line":11,"charByteOffset":42}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":37},"end":{"line":11,"charByteOffset":42}},"hasParens":true}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":11,"charByteOffset":12},"end":{"line":11,"charByteOffset":43}}}},"description":null,"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.CVLFunctionScopeItem","scopeId":9}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"comesFromSpec":true}}}
		AssignExpCmd:203 I161:26 0x0
		AssertCmd:204 true "sanity bounds check on cvl to vm encoding failed (unsigned int elements of a user array)"
		AssignExpCmd:204 R162:21 Apply(hash_3_keccak:bif Apply(skey_basic:bif 0x40) Apply(skey_basic:bif 0x0) Apply(skey_basic:bif 0x0))
		AssignExpCmd:204 R163:21 Apply(skey_add:bif R162:21 0x8)
		AssignExpCmd:205 R164:21 AnnotationExp(Select(CANON64!!159:206 R163:207 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Const","value":"0"},"hashResult":{"#class":"vc.data.TACSymbol.Const","value":"0"}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"100"}}]}})
		AssumeExpCmd Eq(R164:21 0x0 )
		AssignExpCmd:204 B165:22 false
		AnnotationCmd:204 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.DirectStorageLoad","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"B165","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b3","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"test.spec","start":{"line":11,"charByteOffset":12},"end":{"line":11,"charByteOffset":32}}}}
		AssignExpCmd:208 I166:23 CANON66:85
		AssignExpCmd:209 I167:29 0x5
		AssignExpCmd:210 B168:22 false
		AssignExpCmd:211 CANON121:25 true
		AnnotationCmd:204 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":24}
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.CVLSnippetCmd.CVLFunctionEnd","callIndex":3,"name":"workOnSComplexCVL"}}
		AnnotationCmd JSON{"key":{"name":"revert.confluence","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		LabelCmd "join point of revert handling"
		AnnotationCmd JSON{"key":{"name":"call.trace.external.summary.end","type":"analysis.icfg.SummaryStack$SummaryEnd$External","erasureStrategy":"CallTrace"},"value":"rO0ABXNyAC5hbmFseXNpcy5pY2ZnLlN1bW1hcnlTdGFjayRTdW1tYXJ5RW5kJEV4dGVybmFsH6pYA2Le9wICAAJJAAlzdW1tYXJ5SWRMAA5hcHBsaWVkU3VtbWFyeXQALExhbmFseXNpcy9pY2ZnL1N1bW1hcml6YXRpb24kQXBwbGllZFN1bW1hcnk7eHIAJWFuYWx5c2lzLmljZmcuU3VtbWFyeVN0YWNrJFN1bW1hcnlFbmQVlCYDx9Zr6QIAAHhwAAAAAHNyADdhbmFseXNpcy5pY2ZnLlN1bW1hcml6YXRpb24kQXBwbGllZFN1bW1hcnkkTWV0aG9kc0Jsb2NrxBlpQb2eQrwCAAJMAAxzcGVjQ2FsbFN1bW10AC5Mc3BlYy9jdmxhc3QvU3BlY0NhbGxTdW1tYXJ5JEV4cHJlc3NpYmxlSW5DVkw7TAAQc3VtbWFyaXplZE1ldGhvZHQAG0xzcGVjL0NWTCRTdW1tYXJ5U2lnbmF0dXJlO3hwc3IAH3NwZWMuY3ZsYXN0LlNwZWNDYWxsU3VtbWFyeSRFeHCItcAI/3pVHwIAB0wAA2V4cHQAFExzcGVjL2N2bGFzdC9DVkxFeHA7TAAMZXhwZWN0ZWRUeXBldAAQTGphdmEvdXRpbC9MaXN0O0wACWZ1blBhcmFtc3EAfgAKTAAFcmFuZ2V0AA1MdXRpbHMvUmFuZ2U7TAAFc2NvcGV0ABZMc3BlYy9jdmxhc3QvQ1ZMU2NvcGU7TAARc3VtbWFyaXphdGlvbk1vZGV0AC9Mc3BlYy9jdmxhc3QvU3BlY0NhbGxTdW1tYXJ5JFN1bW1hcml6YXRpb25Nb2RlO0wACndpdGhDbGF1c2V0ACxMc3BlYy9jdmxhc3QvU3BlY0NhbGxTdW1tYXJ5JEV4cCRXaXRoQ2xhdXNlO3hyACxzcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnkkRXhwcmVzc2libGVJbkNWTDmMEQXE2U43AgAAeHIAG3NwZWMuY3ZsYXN0LlNwZWNDYWxsU3VtbWFyeZ/hCJ5dxaUBAgAAeHBzcgAnc3BlYy5jdmxhc3QuQ1ZMRXhwJEFwcGx5RXhwJENWTEZ1bmN0aW9uCF/yx/bQMDoCAAVaAAhub1JldmVydEwABGFyZ3NxAH4ACkwAAmlkdAASTGphdmEvbGFuZy9TdHJpbmc7TAAXbWV0aG9kSWRXaXRoQ2FsbENvbnRleHR0AB1Mc3BlYy9jdmxhc3QvU3BlY0RlY2xhcmF0aW9uO0wAA3RhZ3QAF0xzcGVjL2N2bGFzdC9DVkxFeHBUYWc7eHIAG3NwZWMuY3ZsYXN0LkNWTEV4cCRBcHBseUV4cAXcmU1H7VK7AgAAeHIAIXNwZWMuY3ZsYXN0LkNWTEV4cCRBcHBsaWNhdGlvbkV4cAR7vMV6A/l9AgAAeHIAEnNwZWMuY3ZsYXN0LkNWTEV4cAH4n9w14ZOIAgAAeHABc3IAE2phdmEudXRpbC5BcnJheUxpc3R4gdIdmcdhnQMAAUkABHNpemV4cAAAAAJ3BAAAAAJzcgAec3BlYy5jdmxhc3QuQ1ZMRXhwJFZhcmlhYmxlRXhwnRQuSnnYgo0CAARMAAJpZHEAfgATTAAMb3JpZ2luYWxOYW1lcQB+ABNMAAN0YWdxAH4AFUwADXR3b1N0YXRlSW5kZXh0ABtMc3BlYy9jdmxhc3QvVHdvU3RhdGVJbmRleDt4cQB+ABh0AAF4cQB+AB9zcgAVc3BlYy5jdmxhc3QuQ1ZMRXhwVGFn1YsqmFoL+1MCAAVaAAloYXNQYXJlbnNMAAphbm5vdGF0aW9udAAiTHNwZWMvY3ZsYXN0L0V4cHJlc3Npb25Bbm5vdGF0aW9uO0wABXJhbmdlcQB+AAtMAAVzY29wZXEAfgAMTAAEdHlwZXQAFUxzcGVjL2N2bGFzdC9DVkxUeXBlO3hwAHBzcgARdXRpbHMuUmFuZ2UkUmFuZ2V6V69yjESxBgIAA0wAA2VuZHQAFkx1dGlscy9Tb3VyY2VQb3NpdGlvbjtMAAhzcGVjRmlsZXEAfgATTAAFc3RhcnRxAH4AJXhyAAt1dGlscy5SYW5nZegD9PKVZX9XAgAAeHBzcgAUdXRpbHMuU291cmNlUG9zaXRpb26V9OfU6pnEjQIAAkkADmNoYXJCeXRlT2Zmc2V0SQAEbGluZXhwAAAAVQAAAAN0AAl0ZXN0LnNwZWNzcQB+ACgAAABUAAAAA3NyABRzcGVjLmN2bGFzdC5DVkxTY29wZSLJYFjUHV1UAgADTAAWaGFzaENvZGVDYWNoZSRkZWxlZ2F0ZXQADUxrb3RsaW4vTGF6eTtMAAppbm5lclNjb3BlcQB+AAxMAApzY29wZVN0YWNrcQB+AAp4cHNyABprb3RsaW4uSW5pdGlhbGl6ZWRMYXp5SW1wbHvHf/EgKoGNAgABTAAFdmFsdWV0ABJMamF2YS9sYW5nL09iamVjdDt4cHNyABFqYXZhLmxhbmcuSW50ZWdlchLioKT3gYc4AgABSQAFdmFsdWV4cgAQamF2YS5sYW5nLk51bWJlcoaslR0LlOCLAgAAeHDM8ahfc3EAfgAsc3EAfgAvc3EAfgAyTmeNYXNxAH4ALHNxAH4AL3NxAH4AMgAAAB9wc3IAHGtvdGxpbi5jb2xsZWN0aW9ucy5FbXB0eUxpc3SZb8fQp+BgMgIAAHhwc3IAI2phdmEudXRpbC5Db2xsZWN0aW9ucyRTaW5nbGV0b25MaXN0Ku8pEDynm5cCAAFMAAdlbGVtZW50cQB+ADB4cHNyACZzcGVjLmN2bGFzdC5DVkxTY29wZSRJdGVtJEFzdFNjb3BlSXRlbYebp/cG1aGTAgAAeHIAGXNwZWMuY3ZsYXN0LkNWTFNjb3BlJEl0ZW0vA6//njdWRQIAAHhwc3EAfgAaAAAAAncEAAAAAnEAfgBBc3IAK3NwZWMuY3ZsYXN0LkNWTFNjb3BlJEl0ZW0kRXhwcmVzc2lvblN1bW1hcnkPMxqdWl+paAIAAUkAB3Njb3BlSWR4cgApc3BlYy5jdmxhc3QuQ1ZMU2NvcGUkSXRlbSRBU1RFbGVtZW50U2NvcGVSq48RUeQilgIAAUwAB2VsZW1lbnR0ABpMc3BlYy9jdmxhc3QvQ3JlYXRlc1Njb3BlO3hxAH4AQHNxAH4ACHNyACVzcGVjLmN2bGFzdC5DVkxFeHAkVW5yZXNvbHZlZEFwcGx5RXhwNT4Xghu5fcgCAAhaAAxpbnZva2VJc1NhZmVaAA1pbnZva2VJc1dob2xlTAAEYXJnc3EAfgAKTAAEYmFzZXEAfgAJTAANaW52b2tlU3RvcmFnZXQAIExzcGVjL2N2bGFzdC9DVkxFeHAkVmFyaWFibGVFeHA7TAAIbWV0aG9kSWRxAH4AE0wAA3RhZ3EAfgAVTAANdHdvU3RhdGVJbmRleHEAfgAdeHEAfgAXAQBzcQB+ABoAAAACdwQAAAACc3EAfgAccQB+AB9xAH4AH3NxAH4AIABwcQB+ACdxAH4ALnB+cgAZc3BlYy5jdmxhc3QuVHdvU3RhdGVJbmRleAAAAAAAAAAAEgAAeHIADmphdmEubGFuZy5FbnVtAAAAAAAAAAASAAB4cHQAB05FSVRIRVJzcQB+ABx0AAFzcQB+AFNzcQB+ACAAcHNxAH4AJHNxAH4AKAAAAFgAAAADcQB+ACpzcQB+ACgAAABXAAAAA3EAfgAucHEAfgBQeHBzcQB+ABx0AAtsYXN0U3RvcmFnZXEAfgBZc3EAfgAgAHBzcgARdXRpbHMuUmFuZ2UkRW1wdHnEgx6SXniV1wIAAUwAB2NvbW1lbnRxAH4AE3hxAH4AJnQAEmVtcHR5IHN0b3JhZ2UgdHlwZXEAfgAucHEAfgBQdAARd29ya09uU0NvbXBsZXhDVkxzcQB+ACAAcHNxAH4AJHNxAH4AKAAAAFkAAAADcQB+ACpzcQB+ACgAAABCAAAAA3EAfgAucHEAfgBQcHNxAH4AGgAAAAJ3BAAAAAJzcgAZc3BlYy5jdmxhc3QuVk1QYXJhbSROYW1lZABd7PCOutCNAgAETAAEbmFtZXEAfgATTAAMb3JpZ2luYWxOYW1lcQB+ABNMAAVyYW5nZXEAfgALTAAGdm1UeXBldAAuTHNwZWMvY3ZsYXN0L3R5cGVkZXNjcmlwdG9ycy9WTVR5cGVEZXNjcmlwdG9yO3hyABNzcGVjLmN2bGFzdC5WTVBhcmFtoDmogPswXr8CAAB4cHEAfgAfcQB+AB9zcQB+ACRzcQB+ACgAAAAcAAAAA3EAfgAqc3EAfgAoAAAAFgAAAANzcgAzc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJFVJbnRLqHosSzB6DiUCAAFJAAhiaXR3aWR0aHhyAERzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkRVZNSXNvbW9ycGhpY1ZhbHVlVHlwZZbjlXdq3fF/AgAAeHIAOnNwZWMuY3ZsYXN0LnR5cGVkZXNjcmlwdG9ycy5FVk1UeXBlRGVzY3JpcHRvciRFVk1WYWx1ZVR5cGUQ5NL1qK834QIAAHhyAC1zcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3JeVh3cxo4+6AIAAHhwAAABAHNxAH4AZHEAfgBTcQB+AFNzcQB+ACRzcQB+ACgAAAA0AAAAA3EAfgAqc3EAfgAoAAAAHgAAAANzcgBBc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJEVWTVN0cnVjdERlc2NyaXB0b3KmDdePEwDhSgIABEwAC2Nhbm9uaWNhbElkcQB+ABNMAAZmaWVsZHNxAH4ACkwACGxvY2F0aW9udAAyTHNwZWMvY3ZsYXN0L3R5cGVkZXNjcmlwdG9ycy9FVk1Mb2NhdGlvblNwZWNpZmllcjtMAARuYW1lcQB+ABN4cQB+AG50ACVUZXN0Q29udHJhY3Quc29sfFRlc3RDb250cmFjdC5Db21wbGV4c3EAfgAaAAAAA3cEAAAAA3NyAFBzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkRVZNU3RydWN0RGVzY3JpcHRvciRFVk1TdHJ1Y3RFbnRyeR9d3wT4a+GbAgACTAAJZmllbGROYW1lcQB+ABNMAAlmaWVsZFR5cGV0AC9Mc3BlYy9jdmxhc3QvdHlwZWRlc2NyaXB0b3JzL0VWTVR5cGVEZXNjcmlwdG9yO3hwdAACczFzcQB+AHR0ACRUZXN0Q29udHJhY3Quc29sfFRlc3RDb250cmFjdC5TaW1wbGVzcQB+ABoAAAAHdwQAAAAHc3EAfgB5cQB+AB9zcQB+AGsAAAEAc3EAfgB5dAABeXNyADVzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRVZNVHlwZURlc2NyaXB0b3IkYWRkcmVzc8SxMFH2eWoIAgAAeHEAfgBsc3EAfgB5dAACejFzcQB+AGsAAAAIc3EAfgB5dAACejJzcQB+AGsAAAAIc3EAfgB5dAACYjFzcgAyc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkVWTVR5cGVEZXNjcmlwdG9yJGJvb2wFQrLgI3sfyQIAAHhxAH4AbHNxAH4AeXQAAngyc3EAfgBrAAABAHNxAH4AeXQAAmIycQB+AI94cHQAE1Rlc3RDb250cmFjdC5TaW1wbGVzcQB+AHl0AAJzMnNxAH4AdHEAfgB+c3EAfgAaAAAAB3cEAAAAB3NxAH4AeXEAfgAfc3EAfgBrAAABAHNxAH4AeXEAfgCDcQB+AIVzcQB+AHlxAH4Ah3NxAH4AawAAAAhzcQB+AHlxAH4AinNxAH4AawAAAAhzcQB+AHlxAH4AjXEAfgCPc3EAfgB5cQB+AJFzcQB+AGsAAAEAc3EAfgB5cQB+AJRxAH4Aj3hwcQB+AJVzcQB+AHl0AAJiM3EAfgCPeHB0ABRUZXN0Q29udHJhY3QuQ29tcGxleHhzcQB+ACRzcQB+ACgAAABZAAAAA3EAfgAqc3EAfgAoAAAAQgAAAANxAH4ALn5yAC1zcGVjLmN2bGFzdC5TcGVjQ2FsbFN1bW1hcnkkU3VtbWFyaXphdGlvbk1vZGUAAAAAAAAAABIAAHhxAH4AT3QAA0FMTHAAAAAAeHNyABZzcGVjLmN2bGFzdC5DVkxUeXBlJFZNo6s7LR18330CAAJMAAdjb250ZXh0dAArTHNwZWMvY3ZsYXN0L3R5cGVkZXNjcmlwdG9ycy9Gcm9tVk1Db250ZXh0O0wACmRlc2NyaXB0b3JxAH4AZXhyABNzcGVjLmN2bGFzdC5DVkxUeXBldDETlbfBZVACAAB4cHNyAENzcGVjLmN2bGFzdC50eXBlZGVzY3JpcHRvcnMuRnJvbVZNQ29udGV4dCRFeHRlcm5hbFN1bW1hcnlBcmdCaW5kaW5nwnRM6fhMP3sCAAB4cgApc3BlYy5jdmxhc3QudHlwZWRlc2NyaXB0b3JzLkZyb21WTUNvbnRleHTF2vGG93fwZQIAAHhwcQB+AG9xAH4AUHNxAH4AHHEAfgBTcQB+AFNzcQB+ACAAcHEAfgBVcQB+AC5zcQB+AK5xAH4AtHEAfgB2cQB+AFB4cQB+AF5zcgAbc3BlYy5jdmxhc3QuU3BlY0RlY2xhcmF0aW9ujRb0DzyoobcCAAFMAAhtZXRob2RJZHEAfgATeHBxAH4AXnNxAH4AIABzcgAXc3BlYy5jdmxhc3QuQ1ZMRnVuY3Rpb24uWdWoiYfIYQIACUwABWJsb2NrcQB+AApMAA1kZWNsYXJhdGlvbklkcQB+ABNMABJmdW5jdGlvbklkZW50aWZpZXJxAH4AFEwACnBhcmFtVHlwZXNxAH4ACkwABnBhcmFtc3EAfgAKTAAFcmFuZ2VxAH4AC0wABHJldHN0ACFMc3BlYy9jdmxhc3QvQ1ZMVHlwZSRQdXJlQ1ZMVHlwZTtMAAVzY29wZXEAfgAMTAAPdHlwZURlc2NyaXB0aW9ucQB+ABN4cHNxAH4AGgAAAAR3BAAAAARzcgAfc3BlYy5jdmxhc3QuQ1ZMQ21kJFNpbXBsZSRIYXZvY0G+wg9MNoBdAgAETAALYXNzdW1pbmdFeHBxAH4ACUwABXJhbmdlcQB+AAtMAAVzY29wZXEAfgAMTAAHdGFyZ2V0c3EAfgAKeHIAGXNwZWMuY3ZsYXN0LkNWTENtZCRTaW1wbGWA/5FLCuaTSAIAAHhyABJzcGVjLmN2bGFzdC5DVkxDbWR9T7T2R5OokgIAAHhwcHNxAH4AJHNxAH4AKAAAACIAAAAIcQB+ACpzcQB+ACgAAAAEAAAACHNxAH4ALHNxAH4AL3NxAH4AMszxqXZxAH4ANXNxAH4AGgAAAAJ3BAAAAAJxAH4AQXNyAC5zcGVjLmN2bGFzdC5DVkxTY29wZSRJdGVtJENWTEZ1bmN0aW9uU2NvcGVJdGVte1vIQGGDSjkCAAFJAAdzY29wZUlkeHEAfgBEc3EAfgC7c3EAfgAaAAAABHcEAAAABHNxAH4Av3BxAH4Aw3EAfgDGc3EAfgAaAAAAAXcEAAAAAXNyACFzcGVjLmN2bGFzdC5DVkxFeHAkRmllbGRTZWxlY3RFeHBTO4ABfNpZrgIAA0wACWZpZWxkTmFtZXEAfgATTAAJc3RydWN0RXhwcQB+AAlMAAN0YWdxAH4AFXhxAH4AGHEAfgCNc3EAfgDQcQB+AHxzcgAgc3BlYy5jdmxhc3QuQ1ZMRXhwJEFycmF5RGVyZWZFeHDkJNvgbAhgBgIAA0wABWFycmF5cQB+AAlMAAVpbmRleHEAfgAJTAADdGFncQB+ABV4cQB+ABhzcQB+ANB0AAFtc3EAfgAcdAAMdGVzdENvbnRyYWN0cQB+ANhzcQB+ACAAcHNxAH4AJHNxAH4AKAAAABYAAAAIcQB+ACpzcQB+ACgAAAAKAAAACHEAfgDGcHEAfgBQc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAYAAAACHEAfgAqc3EAfgAoAAAACgAAAAhxAH4AxnBzcgAlc3BlYy5jdmxhc3QuQ1ZMRXhwJENvbnN0YW50JE51bWJlckxpdABdlv4jnjYFAgADTAABbnQAFkxqYXZhL21hdGgvQmlnSW50ZWdlcjtMAAlwcmludEhpbnRxAH4AE0wAA3RhZ3EAfgAVeHIAG3NwZWMuY3ZsYXN0LkNWTEV4cCRDb25zdGFudLtVtKlnp5+bAgAAeHEAfgAYc3IAFGphdmEubWF0aC5CaWdJbnRlZ2VyjPyfH6k7+x0DAAZJAAhiaXRDb3VudEkACWJpdExlbmd0aEkAE2ZpcnN0Tm9uemVyb0J5dGVOdW1JAAxsb3dlc3RTZXRCaXRJAAZzaWdudW1bAAltYWduaXR1ZGV0AAJbQnhxAH4AM////////////////v////4AAAAAdXIAAltCrPMX+AYIVOACAAB4cAAAAAB4dAACMTBzcQB+ACAAcHNxAH4AJHNxAH4AKAAAABoAAAAIcQB+ACpzcQB+ACgAAAAZAAAACHEAfgDGcHNxAH4AIABwc3EAfgAkc3EAfgAoAAAAGwAAAAhxAH4AKnNxAH4AKAAAAAoAAAAIcQB+AMZwc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAeAAAACHEAfgAqc3EAfgAoAAAACgAAAAhxAH4AxnBzcQB+ACAAcHNxAH4AJHNxAH4AKAAAACEAAAAIcQB+ACpzcQB+ACgAAAAKAAAACHEAfgDGcHhzcgAqc3BlYy5jdmxhc3QuQ1ZMQ21kJFNpbXBsZSRBc3N1bWVDbWQkQXNzdW1lrChpIcQOwKQCAAZaAA1jb21lc0Zyb21TcGVjWgAQaW52YXJpYW50UHJlQ29uZEwAC2Rlc2NyaXB0aW9ucQB+ABNMAANleHBxAH4ACUwABXJhbmdlcQB+AAtMAAVzY29wZXEAfgAMeHIAI3NwZWMuY3ZsYXN0LkNWTENtZCRTaW1wbGUkQXNzdW1lQ21kb17awtyOC4QCAAB4cQB+AMABAHBzcgAhc3BlYy5jdmxhc3QuQ1ZMRXhwJFJlbG9wRXhwJEVxRXhwSA5Rt59W1MoCAANMAAFscQB+AAlMAAFycQB+AAlMAAN0YWdxAH4AFXhyABtzcGVjLmN2bGFzdC5DVkxFeHAkUmVsb3BFeHDU/s1EWO+7ogIAAHhxAH4AGHNxAH4A0HEAfgCNc3EAfgDQcQB+AHxzcQB+ANNzcQB+ANBxAH4A1nNxAH4AHHEAfgDYcQB+ANhzcQB+ACAAcHNxAH4AJHNxAH4AKAAAABgAAAAJcQB+ACpzcQB+ACgAAAAMAAAACXEAfgDGcHEAfgBQc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAaAAAACXEAfgAqc3EAfgAoAAAADAAAAAlxAH4AxnBzcQB+AOFxAH4A53EAfgDqc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAcAAAACXEAfgAqc3EAfgAoAAAAGwAAAAlxAH4AxnBzcQB+ACAAcHNxAH4AJHNxAH4AKAAAAB0AAAAJcQB+ACpzcQB+ACgAAAAMAAAACXEAfgDGcHNxAH4AIABwc3EAfgAkc3EAfgAoAAAAIAAAAAlxAH4AKnNxAH4AKAAAAAwAAAAJcQB+AMZwc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAjAAAACXEAfgAqc3EAfgAoAAAADAAAAAlxAH4AxnBzcgAvc3BlYy5jdmxhc3QuQ1ZMRXhwJFJlbG9wRXhwJEFyaXRoUmVsb3BFeHAkR3RFeHCKWiySXzW1qwIAA0wAAWxxAH4ACUwAAXJxAH4ACUwAA3RhZ3EAfgAVeHIAKXNwZWMuY3ZsYXN0LkNWTEV4cCRSZWxvcEV4cCRBcml0aFJlbG9wRXhwjuikKS3qy2cCAAB4cQB+AP9zcQB+ABxxAH4AH3EAfgAfc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAApAAAACXEAfgAqc3EAfgAoAAAAKAAAAAlxAH4AxnBxAH4AUHNxAH4A4XNxAH4A5f///////////////v////4AAAABdXEAfgDoAAAAAQN4cQB+AOpzcQB+ACAAcHNxAH4AJHNxAH4AKAAAAC0AAAAJcQB+ACpzcQB+ACgAAAAsAAAACXEAfgDGcHNxAH4AIAFwc3EAfgAkc3EAfgAoAAAALQAAAAlxAH4AKnNxAH4AKAAAACgAAAAJcQB+AMZwc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAuAAAACXEAfgAqc3EAfgAoAAAADAAAAAlxAH4AxnBzcQB+ACRzcQB+ACgAAAAvAAAACXEAfgAqc3EAfgAoAAAABAAAAAlxAH4AxnNxAH4Av3BzcQB+ACRzcQB+ACgAAAAfAAAACnEAfgAqc3EAfgAoAAAABAAAAApxAH4AxnNxAH4AGgAAAAF3BAAAAAFzcQB+ANBxAH4ApnNxAH4A03NxAH4A0HEAfgDWc3EAfgAccQB+ANhxAH4A2HNxAH4AIABwc3EAfgAkc3EAfgAoAAAAFgAAAApxAH4AKnNxAH4AKAAAAAoAAAAKcQB+AMZwcQB+AFBzcQB+ACAAcHNxAH4AJHNxAH4AKAAAABgAAAAKcQB+ACpzcQB+ACgAAAAKAAAACnEAfgDGcHNxAH4A4XEAfgDncQB+AOpzcQB+ACAAcHNxAH4AJHNxAH4AKAAAABoAAAAKcQB+ACpzcQB+ACgAAAAZAAAACnEAfgDGcHNxAH4AIABwc3EAfgAkc3EAfgAoAAAAGwAAAApxAH4AKnNxAH4AKAAAAAoAAAAKcQB+AMZwc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAeAAAACnEAfgAqc3EAfgAoAAAACgAAAApxAH4AxnB4c3EAfgD7AQBwc3EAfgD+c3EAfgDQcQB+AKZzcQB+ANNzcQB+ANBxAH4A1nNxAH4AHHEAfgDYcQB+ANhzcQB+ACAAcHNxAH4AJHNxAH4AKAAAABgAAAALcQB+ACpzcQB+ACgAAAAMAAAAC3EAfgDGcHEAfgBQc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAaAAAAC3EAfgAqc3EAfgAoAAAADAAAAAtxAH4AxnBzcQB+AOFxAH4A53EAfgDqc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAcAAAAC3EAfgAqc3EAfgAoAAAAGwAAAAtxAH4AxnBzcQB+ACAAcHNxAH4AJHNxAH4AKAAAAB0AAAALcQB+ACpzcQB+ACgAAAAMAAAAC3EAfgDGcHNxAH4AIABwc3EAfgAkc3EAfgAoAAAAIAAAAAtxAH4AKnNxAH4AKAAAAAwAAAALcQB+AMZwc3EAfgEfc3EAfgAccQB+AB9xAH4AH3NxAH4AIABwc3EAfgAkc3EAfgAoAAAAJgAAAAtxAH4AKnNxAH4AKAAAACUAAAALcQB+AMZwcQB+AFBzcQB+AOFzcQB+AOX///////////////7////+AAAAAXVxAH4A6AAAAAEFeHEAfgDqc3EAfgAgAHBzcQB+ACRzcQB+ACgAAAAqAAAAC3EAfgAqc3EAfgAoAAAAKQAAAAtxAH4AxnBzcQB+ACABcHNxAH4AJHNxAH4AKAAAACoAAAALcQB+ACpzcQB+ACgAAAAlAAAAC3EAfgDGcHNxAH4AIABwc3EAfgAkc3EAfgAoAAAAKwAAAAtxAH4AKnNxAH4AKAAAAAwAAAALcQB+AMZwc3EAfgAkc3EAfgAoAAAALAAAAAtxAH4AKnNxAH4AKAAAAAQAAAALcQB+AMZ4cQB+AF5zcQB+ALhxAH4AXnNxAH4AGgAAAAJ3BAAAAAJzcgAvc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRQcmltaXRpdmUkVUludEu5C5qOKRJGKQIAAkkACGJpdFdpZHRoSQABa3hyAClzcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBlJFByaW1pdGl2ZQqb2/80fsI7AgAAeHIAH3NwZWMuY3ZsYXN0LkNWTFR5cGUkUHVyZUNWTFR5cGX9BrQWU7YosQIAAHhxAH4AsAAAAQAAAAEAc3IAJnNwZWMuY3ZsYXN0LkNWTFR5cGUkUHVyZUNWTFR5cGUkU3RydWN0NUmhFGkTOYMCAAJMAAZmaWVsZHNxAH4ACkwABG5hbWVxAH4AE3hxAH4BjnNxAH4AGgAAAAN3BAAAAANzcgAyc3BlYy5jdmxhc3QuQ1ZMVHlwZSRQdXJlQ1ZMVHlwZSRTdHJ1Y3QkU3RydWN0RW50cnkzHxoz/bbqDQIAAkwAB2N2bFR5cGVxAH4AvEwACWZpZWxkTmFtZXEAfgATeHBzcQB+AZBzcQB+ABoAAAAHdwQAAAAHc3EAfgGTc3EAfgGMAAABAAAAAQBxAH4AH3NxAH4Bk3NyADtzcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBlJFByaW1pdGl2ZSRBY2NvdW50SWRlbnRpZmllciBFCkT8AptxAgAAeHEAfgGNcQB+AINzcQB+AZNzcQB+AYwAAAAIAAAACHEAfgCHc3EAfgGTc3EAfgGMAAAACAAAAAhxAH4AinNxAH4Bk3NyAC5zcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBlJFByaW1pdGl2ZSRCb29s26vBaNgwss8CAAB4cQB+AY1xAH4AjXNxAH4Bk3NxAH4BjAAAAQAAAAEAcQB+AJFzcQB+AZNxAH4BonEAfgCUeHEAfgCVcQB+AHxzcQB+AZNzcQB+AZBzcQB+ABoAAAAHdwQAAAAHc3EAfgGTc3EAfgGMAAABAAAAAQBxAH4AH3NxAH4Bk3EAfgGbcQB+AINzcQB+AZNzcQB+AYwAAAAIAAAACHEAfgCHc3EAfgGTc3EAfgGMAAAACAAAAAhxAH4AinNxAH4Bk3EAfgGicQB+AI1zcQB+AZNzcQB+AYwAAAEAAAABAHEAfgCRc3EAfgGTcQB+AaJxAH4AlHhxAH4AlXEAfgCXc3EAfgGTcQB+AaJxAH4ApnhxAH4Ap3hzcQB+ABoAAAACdwQAAAACc3IAFHNwZWMuY3ZsYXN0LkNWTFBhcmFtlSBDLCwtTtkCAARMAAJpZHEAfgATTAAKb3JpZ2luYWxJZHEAfgATTAAFcmFuZ2VxAH4AC0wABHR5cGVxAH4AvHhwcQB+AB9xAH4AH3NxAH4AJHNxAH4AKAAAACEAAAAHcQB+ACpzcQB+ACgAAAAbAAAAB3EAfgGPc3EAfgG2cQB+AFNxAH4AU3NxAH4AJHNxAH4AKAAAADkAAAAHcQB+ACpzcQB+ACgAAAAjAAAAB3EAfgGReHNxAH4AJHNxAH4AKAAAAAEAAAAMcQB+ACpzcQB+ACgAAAAAAAAAB3NyACRzcGVjLmN2bGFzdC5DVkxUeXBlJFB1cmVDVkxUeXBlJFZvaWSLoGTVjfh1ZwIAAHhxAH4BjnEAfgDGdAAMQ1ZMIGZ1bmN0aW9uAAAACXhzcQB+ABoAAAABdwQAAAABc3EAfgDQcQB+AI1zcQB+ANBxAH4AfHNxAH4A03NxAH4A0HEAfgDWc3EAfgAccQB+ANhxAH4A2HEAfgDZcQB+AFBxAH4A3XEAfgDkcQB+AO9xAH4A83EAfgD3eHNxAH4A+wEAcHNxAH4A/nNxAH4A0HEAfgCNc3EAfgDQcQB+AHxzcQB+ANNzcQB+ANBxAH4A1nNxAH4AHHEAfgDYcQB+ANhxAH4BBnEAfgBQcQB+AQpxAH4BDnEAfgETcQB+ARdxAH4BG3NxAH4BH3NxAH4AHHEAfgAfcQB+AB9xAH4BI3EAfgBQcQB+ASdxAH4BLnEAfgEycQB+ATZxAH4AxnNxAH4Av3BxAH4BOnEAfgDGc3EAfgAaAAAAAXcEAAAAAXNxAH4A0HEAfgCmc3EAfgDTc3EAfgDQcQB+ANZzcQB+ABxxAH4A2HEAfgDYcQB+AUJxAH4AUHEAfgFGcQB+AUpxAH4BT3EAfgFTeHNxAH4A+wEAcHNxAH4A/nNxAH4A0HEAfgCmc3EAfgDTc3EAfgDQcQB+ANZzcQB+ABxxAH4A2HEAfgDYcQB+AV1xAH4AUHEAfgFhcQB+AWVxAH4BanEAfgFuc3EAfgEfc3EAfgAccQB+AB9xAH4AH3EAfgF0cQB+AFBxAH4BeHEAfgF/cQB+AYNxAH4Bh3EAfgDGeHEAfgBec3EAfgC4cQB+AF5zcQB+ABoAAAACdwQAAAACcQB+AY9xAH4BkXhzcQB+ABoAAAACdwQAAAACcQB+AbdxAH4Bu3hxAH4Bv3EAfgHDcQB+AMZxAH4BxHEAfgBgcQB+AC5xAH4Bw3BzcQB+ABoAAAACdwQAAAACcQB+AGdxAH4AcHhxAH4AqHEAfgAucQB+AKxwc3IAFnNwZWMuQ1ZMJEV4dGVybmFsRXhhY3TnMJk7lNdBOAIAAkwACnNpZ2hhc2hJbnR0ABBMZXZtL1NpZ2hhc2hJbnQ7TAAJc2lnbmF0dXJldAAvTHNwZWMvY3ZsYXN0L1F1YWxpZmllZE1ldGhvZFBhcmFtZXRlclNpZ25hdHVyZTt4cHNyAA5ldm0uU2lnaGFzaEludD27anqQ+KbVAgABTAABbnEAfgDieHBzcQB+AOX///////////////7////+AAAAAXVxAH4A6AAAAASHC/OTeHNyADdzcGVjLmN2bGFzdC5RdWFsaWZpZWRNZXRob2RTaWduYXR1cmUkUXVhbGlmaWVkTWV0aG9kU2lnUBcrUO3kYmwCAANMAAZwYXJhbXNxAH4ACkwAE3F1YWxpZmllZE1ldGhvZE5hbWV0AChMc3BlYy9jdmxhc3QvQ29udHJhY3RGdW5jdGlvbklkZW50aWZpZXI7TAADcmVzcQB+AAp4cHEAfgBjc3IAHXNwZWMuY3ZsYXN0LlF1YWxpZmllZEZ1bmN0aW9u5SlM8uQ5UYMCAAJMAARob3N0dAAeTHNwZWMvY3ZsYXN0L1NvbGlkaXR5Q29udHJhY3Q7TAAIbWV0aG9kSWRxAH4AE3hwc3IAHHNwZWMuY3ZsYXN0LlNvbGlkaXR5Q29udHJhY3QjaX13GoE9ogIAAUwABG5hbWVxAH4AE3hwdAAMVGVzdENvbnRyYWN0dAAId29ya09uUzFxAH4APA=="}
		LabelCmd "Inline CVL/Ghost Function 'workOnSComplexCVL(x,s)'"
		JumpCmd 3_0_0_1_0_0
	}
	Block 3_0_0_1_0_0 Succ [4_0_0_0_0_0] {
		AnnotationCmd:151 JSON{"key":{"name":"tac.decompiler.call-end","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet","branchIndex":3,"branchSource":{"range":{"specFile":"TestContract.sol","start":{"line":22,"charByteOffset":8},"end":{"line":22,"charByteOffset":30}},"content":"this.workOnS1(x, m[0])"}}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet","branchIndex":3}}
		AnnotationCmd:151 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":315,"bytecodeCount":7,"sources":[{"source":0,"begin":367,"end":389},{"source":0,"begin":319,"end":396}]}}
		AnnotationCmd:212 JSON{"key":{"name":"block.source","type":"decompiler.Decompiler$BlockSourceInfo","erasureStrategy":"Canonical"},"value":{"contractName":"TestContract","contractAddress":"ce4604a0000000000000000000000001","contractBytecodeHash":"de50e2ae4804a7eb6a60b6d8b35d3af2a0ce02a09f983d075e9b14a5ae996032","pc":107,"bytecodeCount":2,"sources":[{"source":0,"begin":319,"end":396}]}}
		AssignExpCmd:212 lastHasThrown!!169:69 false
		AssignExpCmd:212 lastReverted!!170:9 false
		AnnotationCmd:212 JSON{"key":{"name":"tac.return.path","type":"tac.MetaMap$Companion$NothingValue","erasureStrategy":"Canonical"},"value":{}}
		AnnotationCmd:144 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.HaltSnippet.Return","range":{"specFile":"TestContract.sol","start":{"line":21,"charByteOffset":4},"end":{"line":23,"charByteOffset":5}}}}
		LabelCmd:144 "End procedure TestContract-workOnS1Ext(uint256)"
		AnnotationCmd:144 JSON{"key":{"name":"call.trace.pop","type":"analysis.icfg.Inliner$CallStack$PopRecord","erasureStrategy":"Canonical"},"value":{"callee":{"contractId":"ce4604a0000000000000000000000001","sigHash":{"n":"4166f100"},"attr":{"#class":"scene.MethodAttribute.Common"}},"calleeId":1}}
	}
	Block 4_0_0_0_0_0 Succ [] {
		AnnotationCmd JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageGlobalChangeSnippet.StorageTakeSnapshot","lhs":{"namePrefix":"lastStorage","tag":{"#class":"tac.Tag.BlockchainState"},"callIndex":0,"meta":[{"key":{"name":"cvl.def.site","type":"spec.CVLDefinitionSite","erasureStrategy":"Canonical"},"value":{"#class":"spec.CVLDefinitionSite.Rule"}},{"key":{"name":"Tac.symbol.keyword","type":"vc.data.TACSymbol$Var$KeywordEntry","erasureStrategy":"Canonical"},"value":{"#class":"vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry","name":"lastStorage"}},{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.VMInternal.BlockchainState"}},{"key":{"name":"cvl","type":"java.lang.Boolean","erasureStrategy":"Canonical"},"value":true},{"key":{"name":"cvl.display","type":"java.lang.String","erasureStrategy":"CallTrace"},"value":"lastStorage"}]}}}
		AnnotationCmd:144 JSON{"key":{"name":"cvl.label.end","type":"java.lang.Integer","erasureStrategy":"Canonical"},"value":20}
		AnnotationCmd:213 JSON{"key":{"name":"cvl.label.start","type":"report.calltrace.CVLReportLabel","erasureStrategy":"CallTrace"},"value":{"#class":"report.calltrace.CVLReportLabel.Cmd","cmd":{"cmd_type":"spec.cvlast.CVLCmd.Simple.Assert","range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":33,"charByteOffset":4},"end":{"line":33,"charByteOffset":32}},"exp":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.ArrayDerefExp","array":{"#class":"spec.cvlast.CVLExp.FieldSelectExp","structExp":{"#class":"spec.cvlast.CVLExp.VariableExp","id":"testContract","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract","name":{"name":"TestContract"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":33,"charByteOffset":11},"end":{"line":33,"charByteOffset":23}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId","instanceId":"ce4604a0000000000000000000000001"}},"twoStateIndex":"NEITHER"},"fieldName":"m","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor","keyType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256},"valueType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"location":null},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":33,"charByteOffset":11},"end":{"line":33,"charByteOffset":25}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"index":{"#class":"spec.cvlast.CVLExp.Constant.NumberLit","n":"0","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral","n":"0"},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":33,"charByteOffset":26},"end":{"line":33,"charByteOffset":27}}}},"tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Complex","location":null,"fields":[{"fieldName":"s1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"s2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor","canonicalId":"TestContract.sol|TestContract.Simple","location":null,"fields":[{"fieldName":"x","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"y","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.address"}},{"fieldName":"z1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"z2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":8}},{"fieldName":"b1","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}},{"fieldName":"x2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK","bitwidth":256}},{"fieldName":"b2","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Simple"}},{"fieldName":"b3","fieldType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"}}],"name":"TestContract.Complex"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":33,"charByteOffset":11},"end":{"line":33,"charByteOffset":28}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"fieldName":"b3","tag":{"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}},"type":{"#class":"spec.cvlast.CVLType.VM","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"},"context":{"#class":"spec.cvlast.typedescriptors.FromVMContext.StateValue"}},"range":{"#class":"utils.Range.Range","specFile":"test.spec","start":{"line":33,"charByteOffset":11},"end":{"line":33,"charByteOffset":31}},"annotation":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"}}},"description":null,"scope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"},{"#class":"spec.cvlast.CVLScope.Item.RuleScopeItem","scopeId":3}],"innerScope":{"scopeStack":[{"#class":"spec.cvlast.CVLScope.Item.AstScopeItem"}],"innerScope":{"scopeStack":[],"innerScope":null}}}}}}
		AssignExpCmd:214 I171:26 0x0
		AssertCmd:215 true "sanity bounds check on cvl to vm encoding failed (unsigned int elements of a user array)"
		AssignExpCmd:215 R172:21 Apply(hash_3_keccak:bif Apply(skey_basic:bif 0x40) Apply(skey_basic:bif 0x0) Apply(skey_basic:bif 0x0))
		AssignExpCmd:215 R173:21 Apply(skey_add:bif R172:21 0x8)
		AssignExpCmd:216 R174:21 AnnotationExp(Select(CANON64!!159:206 R173:217 ) JSON{"key":{"name":"tac.storage.access-paths","type":"analysis.storage.StorageAnalysisResult$AccessPaths","erasureStrategy":"Canonical"},"value":{"paths":[{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.StructAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.MapAccess","base":{"#class":"analysis.storage.StorageAnalysis.AnalysisPath.Root","slot":"0"},"key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"baseSlot":{"#class":"vc.data.TACSymbol.Const","value":"0"},"hashResult":{"#class":"vc.data.TACSymbol.Const","value":"0"}},"offset":{"#class":"analysis.storage.StorageAnalysis.Offset.Bytes","numBytes":"100"}}]}})
		AssignExpCmd:215 B176:22 LNot(Eq(R174:21 0x0 ) )
		AnnotationCmd:215 JSON{"key":{"name":"snippet.cmd","type":"vc.data.SnippetCmd","erasureStrategy":"CallTrace"},"value":{"#class":"vc.data.SnippetCmd.EVMSnippetCmd.StorageSnippet.DirectStorageLoad","value":{"#class":"vc.data.TACSymbol.Var.Full","namePrefix":"B176","tag":{"#class":"tac.Tag.Bool"},"callIndex":0,"meta":[{"key":{"name":"cvl.type","type":"spec.cvlast.CVLType$PureCVLType","erasureStrategy":"CallTrace"},"value":{"#class":"spec.cvlast.CVLType.PureCVLType.Primitive.Bool"}}]},"displayPath":{"#class":"analysis.storage.DisplayPath.FieldAccess","field":"b3","base":{"#class":"analysis.storage.DisplayPath.MapAccess","key":{"#class":"vc.data.TACSymbol.Const","value":"0"},"keyTyp":{"#class":"tac.TACStorageType.IntegralType","typeLabel":"uint256","numBytes":"20","descriptor":{"#class":"ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK","bitwidth":256},"lowerBound":null,"upperBound":null},"base":{"#class":"analysis.storage.DisplayPath.Root","name":"m"}}},"storageType":{"#class":"spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"},"contractInstance":"ce4604a0000000000000000000000001","range":{"specFile":"test.spec","start":{"line":33,"charByteOffset":11},"end":{"line":33,"charByteOffset":31}}}}
		AssertCmd:218 B176:22 "testContract.m[0].b3"
	}
}
Axioms {
}
Metas {
  "0": [
    {
      "key": {
        "name": "tac.is.memory",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacM",
        "maybeTACKeywordOrdinal": 1
      }
    },
    {
      "key": {
        "name": "tacsimplesimple.havocme",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.memory.partition",
        "type": "analysis.pta.abi.UnindexedPartition",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "id": 0
      }
    }
  ],
  "1": [
    {
      "key": {
        "name": "tac.is.memory",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacM",
        "maybeTACKeywordOrdinal": 1
      }
    },
    {
      "key": {
        "name": "tac.memory.partition",
        "type": "analysis.pta.abi.UnindexedPartition",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "id": 0
      }
    }
  ],
  "2": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacM0x40",
        "maybeTACKeywordOrdinal": 39
      }
    },
    {
      "key": {
        "name": "tac.is.reserved.memory.slot.var",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "40"
    }
  ],
  "3": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCodesize",
        "maybeTACKeywordOrdinal": 7
      }
    },
    {
      "key": {
        "name": "tac.codesize",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "4": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 1,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.wordmap-key",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Split",
        "idx": "4"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.calldata.offset",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "5": [
    {
      "key": {
        "name": "tac.is.memory",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacM",
        "maybeTACKeywordOrdinal": 1
      }
    },
    {
      "key": {
        "name": "tac.memory.partition",
        "type": "analysis.pta.abi.UnindexedPartition",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "id": 2
      }
    }
  ],
  "6": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "1"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 0
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 160
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "1"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "7": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "1"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 160
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 8
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "1"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "8": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacAddress",
        "maybeTACKeywordOrdinal": 22
      }
    },
    {
      "key": {
        "name": "tac.env.known-bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 160
    }
  ],
  "9": [
    {
      "key": {
        "name": "tac.last.reverted",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule"
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "lastReverted"
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "lastReverted"
    }
  ],
  "10": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract",
        "name": {
          "name": "TestContract"
        }
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "currentContract"
    }
  ],
  "11": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacExtcodesize",
        "maybeTACKeywordOrdinal": 25
      }
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.is.extcodesize",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "12": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "0"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 256
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "0"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "13": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "1"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 168
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 8
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "1"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "14": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "1"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 176
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "1"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "15": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatasize",
        "maybeTACKeywordOrdinal": 12
      }
    }
  ],
  "16": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacReturndata",
        "maybeTACKeywordOrdinal": 19
      }
    },
    {
      "key": {
        "name": "tac.is.returndata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "17": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule"
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "calledContract"
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "calledContract"
    }
  ],
  "18": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "2"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 256
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "2"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "19": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "3"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 0
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "3"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "20": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON98",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "36"
            }
          }
        ]
      }
    }
  ],
  "21": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "22": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    }
  ],
  "23": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    }
  ],
  "24": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
        "n": "3"
      }
    }
  ],
  "25": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    }
  ],
  "26": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
        "n": "0"
      }
    }
  ],
  "27": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON107",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    }
  ],
  "28": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON113",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    }
  ],
  "29": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
        "n": "5"
      }
    }
  ],
  "30": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON123",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    }
  ],
  "31": [
    {
      "key": {
        "name": "tac.is.memory",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacM",
        "maybeTACKeywordOrdinal": 1
      }
    },
    {
      "key": {
        "name": "tac.memory.partition",
        "type": "analysis.pta.abi.UnindexedPartition",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "id": 3
      }
    }
  ],
  "32": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacBalance",
        "maybeTACKeywordOrdinal": 23
      }
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "33": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "4"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 256
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "4"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "34": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "5"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 0
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 160
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "5"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "35": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "5"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 160
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 8
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "5"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "36": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "5"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 168
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 8
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "5"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "37": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "5"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 176
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "5"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "38": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 1,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "39": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 996
    }
  ],
  "40": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "msg",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "msg",
              "fields": [
                {
                  "fieldName": "sender",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "value",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "sender",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    }
  ],
  "41": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "ecrecover"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "1"
    }
  ],
  "42": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "sha256"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "2"
    }
  ],
  "43": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "identity"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "4"
    }
  ],
  "44": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "TestContract"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "45": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1021
    }
  ],
  "46": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1018
    }
  ],
  "47": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "4"
      }
    }
  ],
  "48": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "49": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "24"
      }
    }
  ],
  "50": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "44"
      }
    }
  ],
  "51": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "64"
      }
    }
  ],
  "52": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "84"
      }
    }
  ],
  "53": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "a4"
      }
    }
  ],
  "54": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "c4"
      }
    }
  ],
  "55": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "e4"
      }
    }
  ],
  "56": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1009
    }
  ],
  "57": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "104"
      }
    }
  ],
  "58": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "124"
      }
    }
  ],
  "59": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "144"
      }
    }
  ],
  "60": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1002
    }
  ],
  "61": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "164"
      }
    }
  ],
  "62": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "184"
      }
    }
  ],
  "63": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "1a4"
      }
    }
  ],
  "64": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "1c4"
      }
    }
  ],
  "65": [
    {
      "key": {
        "name": "tac.decomp-inscalar.sort",
        "type": "tac.DecomposedInputScalarSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "tac.DecomposedInputScalarSort.Simple",
        "byteOffset": "1e4"
      }
    }
  ],
  "66": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1017
    }
  ],
  "67": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1016
    }
  ],
  "68": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1012
    }
  ],
  "69": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule"
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "lastHasThrown"
      }
    },
    {
      "key": {
        "name": "tac.last.has.thrown",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "lastHasThrown"
    }
  ],
  "70": [
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "71": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "0"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "72": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "y",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "20"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "73": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "6"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
        "bitwidth": 256
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "6"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "74": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "7"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 0
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "7"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "75": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "msg",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "msg",
              "fields": [
                {
                  "fieldName": "sender",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "value",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "value",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.msg.value"
    }
  ],
  "76": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "tx",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "tx",
              "fields": [
                {
                  "fieldName": "origin",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "origin",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.tx.origin"
    }
  ],
  "77": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "basefee",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.basefee"
    }
  ],
  "78": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "blobbasefee",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.blobbasefee"
    }
  ],
  "79": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "coinbase",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.coinbase"
    }
  ],
  "80": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "difficulty",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.difficulty"
    }
  ],
  "81": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "gaslimit",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.gaslimit"
    }
  ],
  "82": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "number",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.number"
    }
  ],
  "83": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "block",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "block",
              "fields": [
                {
                  "fieldName": "basefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "blobbasefee",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "coinbase",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "difficulty",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "gaslimit",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "number",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "timestamp",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "timestamp",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.block.timestamp"
    }
  ],
  "84": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "8"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 0
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "8"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "85": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 27
          },
          "end": {
            "line": 7,
            "charByteOffset": 33
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "x"
    }
  ],
  "86": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "x",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s1.x"
    }
  ],
  "87": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "y",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s1.y"
    }
  ],
  "88": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "z1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 8
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 8
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s1.z1"
    }
  ],
  "89": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "z2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 8
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 8
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s1.z2"
    }
  ],
  "90": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "b1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s1.b1"
    }
  ],
  "91": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "x2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s1.x2"
    }
  ],
  "92": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "b2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s1.b2"
    }
  ],
  "93": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "x",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s2.x"
    }
  ],
  "94": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "y",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s2.y"
    }
  ],
  "95": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "z1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 8
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 8
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s2.z1"
    }
  ],
  "96": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "z2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 8
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 8
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s2.z2"
    }
  ],
  "97": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "b1",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s2.b1"
    }
  ],
  "98": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "x2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s2.x2"
    }
  ],
  "99": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "s2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "TestContract.Simple",
              "fields": [
                {
                  "fieldName": "x",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "y",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "z1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "z2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 8
                  }
                },
                {
                  "fieldName": "b1",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                },
                {
                  "fieldName": "x2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                },
                {
                  "fieldName": "b2",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                  }
                }
              ]
            }
          },
          {
            "fieldName": "b2",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.s2.b2"
    }
  ],
  "100": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "TestContract.Complex",
          "fields": [
            {
              "fieldName": "s1",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "s2",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "TestContract.Simple",
                "fields": [
                  {
                    "fieldName": "x",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "y",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "z1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "z2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 8
                    }
                  },
                  {
                    "fieldName": "b1",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  },
                  {
                    "fieldName": "x2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "b2",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "b3",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "b3",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Function",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 7,
            "charByteOffset": 35
          },
          "end": {
            "line": 7,
            "charByteOffset": 57
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "s.b3"
    }
  ],
  "101": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON92",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "36"
            }
          }
        ]
      }
    }
  ],
  "102": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "2"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "103": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "60"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "104": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "4"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "105": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "y",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "a0"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "106": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "6"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "107": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "e0"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "108": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b3",
            "base": {
              "#class": "analysis.storage.DisplayPath.MapAccess",
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "keyTyp": {
                "#class": "tac.TACStorageType.IntegralType",
                "typeLabel": "uint256",
                "numBytes": "20",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                  "bitwidth": 256
                },
                "lowerBound": null,
                "upperBound": null
              },
              "base": {
                "#class": "analysis.storage.DisplayPath.Root",
                "name": "m"
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON36",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "CANON33",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 1,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1009
    }
  ],
  "109": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule"
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "executingContract"
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "executingContract"
    }
  ],
  "110": [
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract",
        "name": {
          "name": "TestContract"
        }
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "testContract"
    }
  ],
  "111": [
    {
      "key": {
        "name": "cvl.struct.path",
        "type": "spec.cvlast.CVLStructPathNode",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "rootStructType": {
          "name": "env",
          "fields": [
            {
              "fieldName": "msg",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "msg",
                "fields": [
                  {
                    "fieldName": "sender",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "value",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "tx",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "tx",
                "fields": [
                  {
                    "fieldName": "origin",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  }
                ]
              }
            },
            {
              "fieldName": "block",
              "cvlType": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
                "name": "block",
                "fields": [
                  {
                    "fieldName": "basefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "blobbasefee",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "coinbase",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                    }
                  },
                  {
                    "fieldName": "difficulty",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "gaslimit",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "number",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  },
                  {
                    "fieldName": "timestamp",
                    "cvlType": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                      "k": 256
                    }
                  }
                ]
              }
            }
          ]
        },
        "fields": [
          {
            "fieldName": "msg",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Struct",
              "name": "msg",
              "fields": [
                {
                  "fieldName": "sender",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
                  }
                },
                {
                  "fieldName": "value",
                  "cvlType": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                    "k": 256
                  }
                }
              ]
            }
          },
          {
            "fieldName": "sender",
            "cvlType": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 30,
            "charByteOffset": 4
          },
          "end": {
            "line": 30,
            "charByteOffset": 10
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.AccountIdentifier"
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "e.msg.sender"
    }
  ],
  "112": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacSighash",
        "maybeTACKeywordOrdinal": 6
      }
    }
  ],
  "113": [
    {
      "key": {
        "name": "cvl.def.site",
        "type": "spec.CVLDefinitionSite",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.CVLDefinitionSite.Rule",
        "range": {
          "#class": "utils.Range.Range",
          "specFile": "test.spec",
          "start": {
            "line": 27,
            "charByteOffset": 21
          },
          "end": {
            "line": 27,
            "charByteOffset": 27
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
        "k": 256
      }
    },
    {
      "key": {
        "name": "cvl",
        "type": "java.lang.Boolean",
        "erasureStrategy": "Canonical"
      },
      "value": true
    },
    {
      "key": {
        "name": "cvl.display",
        "type": "java.lang.String",
        "erasureStrategy": "CallTrace"
      },
      "value": "x"
    }
  ],
  "114": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 0
    }
  ],
  "115": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1
    }
  ],
  "116": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 2
    }
  ],
  "117": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.NonTACKeywordEntry",
        "name": "tacContractAt"
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "TestContract"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "ce4604a0000000000000000000000001"
    },
    {
      "key": {
        "name": "tac.non.zero.var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "118": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 3
    }
  ],
  "119": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 4
    }
  ],
  "120": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 5
    }
  ],
  "121": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 6
    }
  ],
  "122": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.non.zero.var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "123": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCodesize",
        "maybeTACKeywordOrdinal": 7
      }
    },
    {
      "key": {
        "name": "tac.codesize",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    },
    {
      "key": {
        "name": "tac.no.callindex",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.non.zero.var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "124": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 7
    }
  ],
  "125": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    }
  ],
  "126": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 9
    }
  ],
  "127": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 10
    }
  ],
  "128": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 11
    }
  ],
  "129": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 12
    }
  ],
  "130": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 13
    }
  ],
  "131": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 14
    }
  ],
  "132": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 15
    }
  ],
  "133": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 16
    }
  ],
  "134": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 17
    }
  ],
  "135": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 18
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 28,
          "charByteOffset": 4
        },
        "end": {
          "line": 28,
          "charByteOffset": 18
        }
      }
    }
  ],
  "136": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "x",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 28,
                "charByteOffset": 12
              },
              "end": {
                "line": 28,
                "charByteOffset": 13
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 28,
          "charByteOffset": 4
        },
        "end": {
          "line": 28,
          "charByteOffset": 18
        }
      }
    }
  ],
  "137": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "3",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "3"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 28,
                "charByteOffset": 16
              },
              "end": {
                "line": 28,
                "charByteOffset": 17
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 28,
          "charByteOffset": 4
        },
        "end": {
          "line": 28,
          "charByteOffset": 18
        }
      }
    }
  ],
  "138": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.LtExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "x",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 28,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 28,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "3"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 28,
                  "charByteOffset": 16
                },
                "end": {
                  "line": 28,
                  "charByteOffset": 17
                }
              }
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 28,
                "charByteOffset": 12
              },
              "end": {
                "line": 28,
                "charByteOffset": 17
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I34",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0,
            "meta": [
              {
                "key": {
                  "name": "cvl.type",
                  "type": "spec.cvlast.CVLType$PureCVLType",
                  "erasureStrategy": "CallTrace"
                },
                "value": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                  "k": 256
                }
              }
            ]
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "x",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 28,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 28,
                  "charByteOffset": 13
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "3"
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                    "scopeId": 3
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "3"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 28,
                  "charByteOffset": 16
                },
                "end": {
                  "line": 28,
                  "charByteOffset": 17
                }
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 28,
          "charByteOffset": 4
        },
        "end": {
          "line": 28,
          "charByteOffset": 18
        }
      }
    }
  ],
  "139": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 28,
          "charByteOffset": 4
        },
        "end": {
          "line": 28,
          "charByteOffset": 18
        }
      }
    }
  ],
  "140": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 19
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 30,
          "charByteOffset": 4
        },
        "end": {
          "line": 30,
          "charByteOffset": 10
        }
      }
    }
  ],
  "141": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 30,
          "charByteOffset": 4
        },
        "end": {
          "line": 30,
          "charByteOffset": 10
        }
      }
    }
  ],
  "142": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 20
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "143": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "x",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 31,
                "charByteOffset": 19
              },
              "end": {
                "line": 31,
                "charByteOffset": 20
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "144": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "145": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 0,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.wordmap-key",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Split",
        "idx": "4"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.calldata.offset",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "146": [
    {
      "key": {
        "name": "tac.transfers.balance",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "147": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacAddress",
        "maybeTACKeywordOrdinal": 22
      }
    },
    {
      "key": {
        "name": "tac.env.known-bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 160
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "TestContract"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "ce4604a0000000000000000000000001"
    },
    {
      "key": {
        "name": "tac.non.zero.var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "148": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 25,
        "len": 1929,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "149": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 319,
        "len": 77,
        "jumpType": "ENTER",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "150": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 384,
        "len": 4,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "151": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "152": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "ENTER",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "153": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize!!39",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 0,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.wordmap-key",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Split",
        "idx": "4"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.calldata.offset",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "154": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "0"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.call-graph.address-read",
        "type": "analysis.icfg.CallGraphBuilder$ContractStorageRead",
        "erasureStrategy": "Canonical"
      },
      "value": "rO0ABXNyADJhbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ29udHJhY3RTdG9yYWdlUmVhZJo5HPv1EkgqAgABSQACaWR4cAAAAAA="
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "155": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "0"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "156": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "1"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.call-graph.address-read",
        "type": "analysis.icfg.CallGraphBuilder$ContractStorageRead",
        "erasureStrategy": "Canonical"
      },
      "value": "rO0ABXNyADJhbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ29udHJhY3RTdG9yYWdlUmVhZJo5HPv1EkgqAgABSQACaWR4cAAAAAE="
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "157": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "y",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "20"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "158": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "z1",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "34"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "159": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "z2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "35"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "160": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b1",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "36"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "161": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "2"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.call-graph.address-read",
        "type": "analysis.icfg.CallGraphBuilder$ContractStorageRead",
        "erasureStrategy": "Canonical"
      },
      "value": "rO0ABXNyADJhbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ29udHJhY3RTdG9yYWdlUmVhZJo5HPv1EkgqAgABSQACaWR4cAAAAAI="
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "162": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "2"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "163": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "3"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "164": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s1",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "60"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "165": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "4"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.call-graph.address-read",
        "type": "analysis.icfg.CallGraphBuilder$ContractStorageRead",
        "erasureStrategy": "Canonical"
      },
      "value": "rO0ABXNyADJhbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ29udHJhY3RTdG9yYWdlUmVhZJo5HPv1EkgqAgABSQACaWR4cAAAAAM="
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "166": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "4"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "167": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "5"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.call-graph.address-read",
        "type": "analysis.icfg.CallGraphBuilder$ContractStorageRead",
        "erasureStrategy": "Canonical"
      },
      "value": "rO0ABXNyADJhbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ29udHJhY3RTdG9yYWdlUmVhZJo5HPv1EkgqAgABSQACaWR4cAAAAAQ="
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "168": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "y",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "a0"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "169": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "z1",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "b4"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "170": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "z2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "b5"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "171": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b1",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "b6"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "172": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "6"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.call-graph.address-read",
        "type": "analysis.icfg.CallGraphBuilder$ContractStorageRead",
        "erasureStrategy": "Canonical"
      },
      "value": "rO0ABXNyADJhbmFseXNpcy5pY2ZnLkNhbGxHcmFwaEJ1aWxkZXIkQ29udHJhY3RTdG9yYWdlUmVhZJo5HPv1EkgqAgABSQACaWR4cAAAAAU="
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "173": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "x2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Words",
              "numWords": "6"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "174": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "7"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "175": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b2",
            "base": {
              "#class": "analysis.storage.DisplayPath.FieldAccess",
              "field": "s2",
              "base": {
                "#class": "analysis.storage.DisplayPath.MapAccess",
                "key": {
                  "#class": "vc.data.TACSymbol.Const",
                  "value": "0"
                },
                "keyTyp": {
                  "#class": "tac.TACStorageType.IntegralType",
                  "typeLabel": "uint256",
                  "numBytes": "20",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                    "bitwidth": 256
                  },
                  "lowerBound": null,
                  "upperBound": null
                },
                "base": {
                  "#class": "analysis.storage.DisplayPath.Root",
                  "name": "m"
                }
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "e0"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1003
    }
  ],
  "176": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 367,
        "len": 22,
        "jumpType": "REGULAR",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.node",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "8"
          }
        ]
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    },
    {
      "key": {
        "name": "tac.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.printer",
        "type": "instrumentation.StoragePathAnnotation$StoragePathPrinter",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "177": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.storage.pretty.paths",
        "type": "analysis.storage.DisplayPaths",
        "erasureStrategy": "Erased"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.DisplayPath.FieldAccess",
            "field": "b3",
            "base": {
              "#class": "analysis.storage.DisplayPath.MapAccess",
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "keyTyp": {
                "#class": "tac.TACStorageType.IntegralType",
                "typeLabel": "uint256",
                "numBytes": "20",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$UIntK",
                  "bitwidth": 256
                },
                "lowerBound": null,
                "upperBound": null
              },
              "base": {
                "#class": "analysis.storage.DisplayPath.Root",
                "name": "m"
              }
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R10",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  }
                ]
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "R53",
                "tag": {
                  "#class": "tac.Tag.Bit256"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "Tac.symbol.keyword",
                      "type": "vc.data.TACSymbol$Var$KeywordEntry",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                      "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                      "name": "L",
                      "maybeTACKeywordOrdinal": 45
                    }
                  },
                  {
                    "key": {
                      "name": "tac.is-temp-var",
                      "type": "tac.MetaMap$Companion$NothingValue",
                      "erasureStrategy": "Canonical"
                    },
                    "value": {
                    }
                  },
                  {
                    "key": {
                      "name": "tac.stack.height",
                      "type": "java.lang.Integer",
                      "erasureStrategy": "Canonical"
                    },
                    "value": 1018
                  }
                ]
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1009
    }
  ],
  "178": [
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "L",
        "maybeTACKeywordOrdinal": 45
      }
    },
    {
      "key": {
        "name": "tac.contract.sym.addr.name",
        "type": "java.lang.String",
        "erasureStrategy": "Erased"
      },
      "value": "TestContract"
    },
    {
      "key": {
        "name": "tac.contract.sym.addr",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Erased"
      },
      "value": "ce4604a0000000000000000000000001"
    },
    {
      "key": {
        "name": "tac.stack.height",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 1021
    },
    {
      "key": {
        "name": "tac.non.zero.var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "179": [
    {
      "key": {
        "name": "tac.immutable.array",
        "type": "vc.data.ImmutableBound",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "sym": {
          "#class": "vc.data.TACSymbol.Var.Full",
          "namePrefix": "tacCalldatasize!!3",
          "tag": {
            "#class": "tac.Tag.Bit256"
          },
          "callIndex": 0,
          "meta": [
            {
              "key": {
                "name": "Tac.symbol.keyword",
                "type": "vc.data.TACSymbol$Var$KeywordEntry",
                "erasureStrategy": "Canonical"
              },
              "value": {
                "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
                "name": "tacCalldatasize",
                "maybeTACKeywordOrdinal": 12
              }
            }
          ]
        }
      }
    },
    {
      "key": {
        "name": "Tac.symbol.keyword",
        "type": "vc.data.TACSymbol$Var$KeywordEntry",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.TACSymbol.Var.KeywordEntry.TACKeywordEntry",
        "name": "tacCalldatabuf",
        "maybeTACKeywordOrdinal": 15
      }
    },
    {
      "key": {
        "name": "tac.wordmap-key",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Split",
        "idx": "4"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 256
    },
    {
      "key": {
        "name": "tac.calldata.offset",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "4"
    },
    {
      "key": {
        "name": "tac.is.calldata",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    }
  ],
  "180": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 21
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 8,
          "charByteOffset": 4
        },
        "end": {
          "line": 8,
          "charByteOffset": 34
        }
      }
    }
  ],
  "181": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "0",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "0"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 8,
                "charByteOffset": 25
              },
              "end": {
                "line": 8,
                "charByteOffset": 26
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 8,
          "charByteOffset": 4
        },
        "end": {
          "line": 8,
          "charByteOffset": 34
        }
      }
    }
  ],
  "182": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 8,
          "charByteOffset": 4
        },
        "end": {
          "line": 8,
          "charByteOffset": 34
        }
      }
    }
  ],
  "183": [
    {
      "key": {
        "name": "tac.direct.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 8,
          "charByteOffset": 4
        },
        "end": {
          "line": 8,
          "charByteOffset": 34
        }
      }
    }
  ],
  "184": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "I139",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "36"
            }
          }
        ]
      }
    }
  ],
  "185": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.BoolLit",
          "b": "1",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "range": {
              "#class": "utils.Range.Empty",
              "comment": "autogenerated bool expression at test.spec:9:5"
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 8,
          "charByteOffset": 4
        },
        "end": {
          "line": 8,
          "charByteOffset": 34
        }
      }
    }
  ],
  "186": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 22
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "187": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "0",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "0"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 9,
                "charByteOffset": 27
              },
              "end": {
                "line": 9,
                "charByteOffset": 28
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "188": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "189": [
    {
      "key": {
        "name": "tac.direct.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "190": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "1"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 176
      }
    },
    {
      "key": {
        "name": "tac.direct.storage.access.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "1"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "191": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "I146",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "36"
            }
          }
        ]
      }
    }
  ],
  "192": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "x",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 9,
                "charByteOffset": 40
              },
              "end": {
                "line": 9,
                "charByteOffset": 41
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "193": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "3",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "3"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 9,
                "charByteOffset": 44
              },
              "end": {
                "line": 9,
                "charByteOffset": 45
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "194": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "x",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 40
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 41
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "3"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 44
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 45
                }
              }
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 9,
                "charByteOffset": 40
              },
              "end": {
                "line": 9,
                "charByteOffset": 45
              }
            },
            "hasParens": true
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I151",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0,
            "meta": [
              {
                "key": {
                  "name": "cvl.type",
                  "type": "spec.cvlast.CVLType$PureCVLType",
                  "erasureStrategy": "CallTrace"
                },
                "value": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                  "k": 256
                }
              }
            ]
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "x",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 40
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 41
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "3"
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "3"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 44
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 45
                }
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "195": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.EqExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.FieldSelectExp",
            "structExp": {
              "#class": "spec.cvlast.CVLExp.FieldSelectExp",
              "structExp": {
                "#class": "spec.cvlast.CVLExp.ArrayDerefExp",
                "array": {
                  "#class": "spec.cvlast.CVLExp.FieldSelectExp",
                  "structExp": {
                    "#class": "spec.cvlast.CVLExp.VariableExp",
                    "id": "testContract",
                    "tag": {
                      "scope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          },
                          {
                            "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                            "scopeId": 9
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                            {
                              "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                            }
                          ],
                          "innerScope": {
                            "scopeStack": [
                            ],
                            "innerScope": null
                          }
                        }
                      },
                      "type": {
                        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract",
                        "name": {
                          "name": "TestContract"
                        }
                      },
                      "range": {
                        "#class": "utils.Range.Range",
                        "specFile": "test.spec",
                        "start": {
                          "line": 9,
                          "charByteOffset": 12
                        },
                        "end": {
                          "line": 9,
                          "charByteOffset": 24
                        }
                      },
                      "annotation": {
                        "#class": "ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId",
                        "instanceId": "ce4604a0000000000000000000000001"
                      }
                    },
                    "twoStateIndex": "NEITHER"
                  },
                  "fieldName": "m",
                  "tag": {
                    "scope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        },
                        {
                          "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                          "scopeId": 9
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                          ],
                          "innerScope": null
                        }
                      }
                    },
                    "type": {
                      "#class": "spec.cvlast.CVLType.VM",
                      "descriptor": {
                        "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor",
                        "keyType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 256
                        },
                        "valueType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                          "canonicalId": "TestContract.sol|TestContract.Complex",
                          "location": null,
                          "fields": [
                            {
                              "fieldName": "s1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                                "canonicalId": "TestContract.sol|TestContract.Simple",
                                "location": null,
                                "fields": [
                                  {
                                    "fieldName": "x",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "y",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                    }
                                  },
                                  {
                                    "fieldName": "z1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "z2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "b1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  },
                                  {
                                    "fieldName": "x2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "b2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  }
                                ],
                                "name": "TestContract.Simple"
                              }
                            },
                            {
                              "fieldName": "s2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                                "canonicalId": "TestContract.sol|TestContract.Simple",
                                "location": null,
                                "fields": [
                                  {
                                    "fieldName": "x",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "y",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                    }
                                  },
                                  {
                                    "fieldName": "z1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "z2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "b1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  },
                                  {
                                    "fieldName": "x2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "b2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  }
                                ],
                                "name": "TestContract.Simple"
                              }
                            },
                            {
                              "fieldName": "b3",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            }
                          ],
                          "name": "TestContract.Complex"
                        },
                        "location": null
                      },
                      "context": {
                        "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                      }
                    },
                    "range": {
                      "#class": "utils.Range.Range",
                      "specFile": "test.spec",
                      "start": {
                        "line": 9,
                        "charByteOffset": 12
                      },
                      "end": {
                        "line": 9,
                        "charByteOffset": 26
                      }
                    },
                    "annotation": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                    }
                  }
                },
                "index": {
                  "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
                  "n": "0",
                  "tag": {
                    "scope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        },
                        {
                          "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                          "scopeId": 9
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                          ],
                          "innerScope": null
                        }
                      }
                    },
                    "type": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    },
                    "range": {
                      "#class": "utils.Range.Range",
                      "specFile": "test.spec",
                      "start": {
                        "line": 9,
                        "charByteOffset": 27
                      },
                      "end": {
                        "line": 9,
                        "charByteOffset": 28
                      }
                    }
                  }
                },
                "tag": {
                  "scope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      },
                      {
                        "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                        "scopeId": 9
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                        ],
                        "innerScope": null
                      }
                    }
                  },
                  "type": {
                    "#class": "spec.cvlast.CVLType.VM",
                    "descriptor": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor",
                      "canonicalId": "TestContract.sol|TestContract.Complex",
                      "location": null,
                      "fields": [
                        {
                          "fieldName": "s1",
                          "fieldType": {
                            "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                            "canonicalId": "TestContract.sol|TestContract.Simple",
                            "location": null,
                            "fields": [
                              {
                                "fieldName": "x",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "y",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                }
                              },
                              {
                                "fieldName": "z1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "z2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "b1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              },
                              {
                                "fieldName": "x2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "b2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              }
                            ],
                            "name": "TestContract.Simple"
                          }
                        },
                        {
                          "fieldName": "s2",
                          "fieldType": {
                            "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                            "canonicalId": "TestContract.sol|TestContract.Simple",
                            "location": null,
                            "fields": [
                              {
                                "fieldName": "x",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "y",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                }
                              },
                              {
                                "fieldName": "z1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "z2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "b1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              },
                              {
                                "fieldName": "x2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "b2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              }
                            ],
                            "name": "TestContract.Simple"
                          }
                        },
                        {
                          "fieldName": "b3",
                          "fieldType": {
                            "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                          }
                        }
                      ],
                      "name": "TestContract.Complex"
                    },
                    "context": {
                      "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                    }
                  },
                  "range": {
                    "#class": "utils.Range.Range",
                    "specFile": "test.spec",
                    "start": {
                      "line": 9,
                      "charByteOffset": 12
                    },
                    "end": {
                      "line": 9,
                      "charByteOffset": 29
                    }
                  },
                  "annotation": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                  }
                }
              },
              "fieldName": "s1",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.VM",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor",
                    "canonicalId": "TestContract.sol|TestContract.Simple",
                    "location": null,
                    "fields": [
                      {
                        "fieldName": "x",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 256
                        }
                      },
                      {
                        "fieldName": "y",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                        }
                      },
                      {
                        "fieldName": "z1",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 8
                        }
                      },
                      {
                        "fieldName": "z2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 8
                        }
                      },
                      {
                        "fieldName": "b1",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                        }
                      },
                      {
                        "fieldName": "x2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 256
                        }
                      },
                      {
                        "fieldName": "b2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                        }
                      }
                    ],
                    "name": "TestContract.Simple"
                  },
                  "context": {
                    "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                  }
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 9,
                    "charByteOffset": 12
                  },
                  "end": {
                    "line": 9,
                    "charByteOffset": 32
                  }
                },
                "annotation": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                }
              }
            },
            "fieldName": "b1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                }
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 35
                }
              },
              "annotation": {
                "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
              }
            }
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
            "l": {
              "#class": "spec.cvlast.CVLExp.VariableExp",
              "id": "x",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                  "k": 256
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 9,
                    "charByteOffset": 40
                  },
                  "end": {
                    "line": 9,
                    "charByteOffset": 41
                  }
                }
              },
              "twoStateIndex": "NEITHER"
            },
            "r": {
              "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
              "n": "3",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                  "n": "3"
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 9,
                    "charByteOffset": 44
                  },
                  "end": {
                    "line": 9,
                    "charByteOffset": 45
                  }
                }
              }
            },
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 40
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 45
                }
              },
              "hasParens": true
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 9,
                "charByteOffset": 12
              },
              "end": {
                "line": 9,
                "charByteOffset": 46
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "0",
            "tag": {
              "#class": "tac.Tag.Bool"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.FieldSelectExp",
            "structExp": {
              "#class": "spec.cvlast.CVLExp.FieldSelectExp",
              "structExp": {
                "#class": "spec.cvlast.CVLExp.ArrayDerefExp",
                "array": {
                  "#class": "spec.cvlast.CVLExp.FieldSelectExp",
                  "structExp": {
                    "#class": "spec.cvlast.CVLExp.VariableExp",
                    "id": "testContract",
                    "tag": {
                      "scope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          },
                          {
                            "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                            "scopeId": 9
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                            {
                              "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                            }
                          ],
                          "innerScope": {
                            "scopeStack": [
                            ],
                            "innerScope": null
                          }
                        }
                      },
                      "type": {
                        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract",
                        "name": {
                          "name": "TestContract"
                        }
                      },
                      "range": {
                        "#class": "utils.Range.Range",
                        "specFile": "test.spec",
                        "start": {
                          "line": 9,
                          "charByteOffset": 12
                        },
                        "end": {
                          "line": 9,
                          "charByteOffset": 24
                        }
                      },
                      "annotation": {
                        "#class": "ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId",
                        "instanceId": "ce4604a0000000000000000000000001"
                      }
                    },
                    "twoStateIndex": "NEITHER"
                  },
                  "fieldName": "m",
                  "tag": {
                    "scope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        },
                        {
                          "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                          "scopeId": 9
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                          ],
                          "innerScope": null
                        }
                      }
                    },
                    "type": {
                      "#class": "spec.cvlast.CVLType.VM",
                      "descriptor": {
                        "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor",
                        "keyType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 256
                        },
                        "valueType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                          "canonicalId": "TestContract.sol|TestContract.Complex",
                          "location": null,
                          "fields": [
                            {
                              "fieldName": "s1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                                "canonicalId": "TestContract.sol|TestContract.Simple",
                                "location": null,
                                "fields": [
                                  {
                                    "fieldName": "x",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "y",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                    }
                                  },
                                  {
                                    "fieldName": "z1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "z2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "b1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  },
                                  {
                                    "fieldName": "x2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "b2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  }
                                ],
                                "name": "TestContract.Simple"
                              }
                            },
                            {
                              "fieldName": "s2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                                "canonicalId": "TestContract.sol|TestContract.Simple",
                                "location": null,
                                "fields": [
                                  {
                                    "fieldName": "x",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "y",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                    }
                                  },
                                  {
                                    "fieldName": "z1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "z2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 8
                                    }
                                  },
                                  {
                                    "fieldName": "b1",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  },
                                  {
                                    "fieldName": "x2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                      "bitwidth": 256
                                    }
                                  },
                                  {
                                    "fieldName": "b2",
                                    "fieldType": {
                                      "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                    }
                                  }
                                ],
                                "name": "TestContract.Simple"
                              }
                            },
                            {
                              "fieldName": "b3",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            }
                          ],
                          "name": "TestContract.Complex"
                        },
                        "location": null
                      },
                      "context": {
                        "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                      }
                    },
                    "range": {
                      "#class": "utils.Range.Range",
                      "specFile": "test.spec",
                      "start": {
                        "line": 9,
                        "charByteOffset": 12
                      },
                      "end": {
                        "line": 9,
                        "charByteOffset": 26
                      }
                    },
                    "annotation": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                    }
                  }
                },
                "index": {
                  "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
                  "n": "0",
                  "tag": {
                    "scope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        },
                        {
                          "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                          "scopeId": 9
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                          ],
                          "innerScope": null
                        }
                      }
                    },
                    "type": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    },
                    "range": {
                      "#class": "utils.Range.Range",
                      "specFile": "test.spec",
                      "start": {
                        "line": 9,
                        "charByteOffset": 27
                      },
                      "end": {
                        "line": 9,
                        "charByteOffset": 28
                      }
                    }
                  }
                },
                "tag": {
                  "scope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      },
                      {
                        "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                        "scopeId": 9
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                        ],
                        "innerScope": null
                      }
                    }
                  },
                  "type": {
                    "#class": "spec.cvlast.CVLType.VM",
                    "descriptor": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor",
                      "canonicalId": "TestContract.sol|TestContract.Complex",
                      "location": null,
                      "fields": [
                        {
                          "fieldName": "s1",
                          "fieldType": {
                            "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                            "canonicalId": "TestContract.sol|TestContract.Simple",
                            "location": null,
                            "fields": [
                              {
                                "fieldName": "x",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "y",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                }
                              },
                              {
                                "fieldName": "z1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "z2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "b1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              },
                              {
                                "fieldName": "x2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "b2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              }
                            ],
                            "name": "TestContract.Simple"
                          }
                        },
                        {
                          "fieldName": "s2",
                          "fieldType": {
                            "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                            "canonicalId": "TestContract.sol|TestContract.Simple",
                            "location": null,
                            "fields": [
                              {
                                "fieldName": "x",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "y",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                }
                              },
                              {
                                "fieldName": "z1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "z2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 8
                                }
                              },
                              {
                                "fieldName": "b1",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              },
                              {
                                "fieldName": "x2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                  "bitwidth": 256
                                }
                              },
                              {
                                "fieldName": "b2",
                                "fieldType": {
                                  "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                }
                              }
                            ],
                            "name": "TestContract.Simple"
                          }
                        },
                        {
                          "fieldName": "b3",
                          "fieldType": {
                            "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                          }
                        }
                      ],
                      "name": "TestContract.Complex"
                    },
                    "context": {
                      "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                    }
                  },
                  "range": {
                    "#class": "utils.Range.Range",
                    "specFile": "test.spec",
                    "start": {
                      "line": 9,
                      "charByteOffset": 12
                    },
                    "end": {
                      "line": 9,
                      "charByteOffset": 29
                    }
                  },
                  "annotation": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                  }
                }
              },
              "fieldName": "s1",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.VM",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor",
                    "canonicalId": "TestContract.sol|TestContract.Simple",
                    "location": null,
                    "fields": [
                      {
                        "fieldName": "x",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 256
                        }
                      },
                      {
                        "fieldName": "y",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                        }
                      },
                      {
                        "fieldName": "z1",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 8
                        }
                      },
                      {
                        "fieldName": "z2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 8
                        }
                      },
                      {
                        "fieldName": "b1",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                        }
                      },
                      {
                        "fieldName": "x2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                          "bitwidth": 256
                        }
                      },
                      {
                        "fieldName": "b2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                        }
                      }
                    ],
                    "name": "TestContract.Simple"
                  },
                  "context": {
                    "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                  }
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 9,
                    "charByteOffset": 12
                  },
                  "end": {
                    "line": 9,
                    "charByteOffset": 32
                  }
                },
                "annotation": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                }
              }
            },
            "fieldName": "b1",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                }
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 35
                }
              },
              "annotation": {
                "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
              }
            }
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "0",
            "tag": {
              "#class": "tac.Tag.Bool"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
            "l": {
              "#class": "spec.cvlast.CVLExp.VariableExp",
              "id": "x",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                  "k": 256
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 9,
                    "charByteOffset": 40
                  },
                  "end": {
                    "line": 9,
                    "charByteOffset": 41
                  }
                }
              },
              "twoStateIndex": "NEITHER"
            },
            "r": {
              "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
              "n": "3",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                  "n": "3"
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 9,
                    "charByteOffset": 44
                  },
                  "end": {
                    "line": 9,
                    "charByteOffset": 45
                  }
                }
              }
            },
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 9,
                  "charByteOffset": 40
                },
                "end": {
                  "line": 9,
                  "charByteOffset": 45
                }
              },
              "hasParens": true
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 9,
          "charByteOffset": 4
        },
        "end": {
          "line": 9,
          "charByteOffset": 47
        }
      }
    }
  ],
  "196": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 23
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 10,
          "charByteOffset": 4
        },
        "end": {
          "line": 10,
          "charByteOffset": 31
        }
      }
    }
  ],
  "197": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "0",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "0"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 10,
                "charByteOffset": 25
              },
              "end": {
                "line": 10,
                "charByteOffset": 26
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 10,
          "charByteOffset": 4
        },
        "end": {
          "line": 10,
          "charByteOffset": 31
        }
      }
    }
  ],
  "198": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 10,
          "charByteOffset": 4
        },
        "end": {
          "line": 10,
          "charByteOffset": 31
        }
      }
    }
  ],
  "199": [
    {
      "key": {
        "name": "tac.direct.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 10,
          "charByteOffset": 4
        },
        "end": {
          "line": 10,
          "charByteOffset": 31
        }
      }
    }
  ],
  "200": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "I154",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    }
  ],
  "201": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.BoolLit",
          "b": "1",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "range": {
              "#class": "utils.Range.Empty",
              "comment": "autogenerated bool expression at test.spec:11:5"
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 10,
          "charByteOffset": 4
        },
        "end": {
          "line": 10,
          "charByteOffset": 31
        }
      }
    }
  ],
  "202": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 24
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "203": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "0",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "0"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 11,
                "charByteOffset": 27
              },
              "end": {
                "line": 11,
                "charByteOffset": 28
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "204": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "205": [
    {
      "key": {
        "name": "tac.direct.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "206": [
    {
      "key": {
        "name": "tac.storage.non-indexed-path.family",
        "type": "analysis.storage.StorageAnalysisResult$StoragePaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "storagePaths": [
          {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
                "slot": "0"
              }
            },
            "offset": "8"
          }
        ]
      }
    },
    {
      "key": {
        "name": "tac.scalarization.sort",
        "type": "vc.data.ScalarizationSort",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "vc.data.ScalarizationSort.Packed",
        "packedStart": {
          "#class": "vc.data.ScalarizationSort.UnscalarizedBuffer"
        },
        "start": 0
      }
    },
    {
      "key": {
        "name": "tac.direct.storage.access.type",
        "type": "spec.cvlast.CVLType$PureCVLType",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.bit-width",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 8
    },
    {
      "key": {
        "name": "tac.slot.type",
        "type": "spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMValueType",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
      }
    },
    {
      "key": {
        "name": "tac.storage.non-indexed-path",
        "type": "analysis.storage.StorageAnalysisResult$NonIndexedPath",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.StructAccess",
        "base": {
          "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.MapAccess",
          "base": {
            "#class": "analysis.storage.StorageAnalysisResult.NonIndexedPath.Root",
            "slot": "0"
          }
        },
        "offset": "8"
      }
    },
    {
      "key": {
        "name": "tac.storage",
        "type": "java.math.BigInteger",
        "erasureStrategy": "Canonical"
      },
      "value": "ce4604a0000000000000000000000001"
    }
  ],
  "207": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "I161",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    }
  ],
  "208": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.VariableExp",
          "id": "x",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
              "k": 256
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 11,
                "charByteOffset": 37
              },
              "end": {
                "line": 11,
                "charByteOffset": 38
              }
            }
          },
          "twoStateIndex": "NEITHER"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "209": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "5",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "5"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 11,
                "charByteOffset": 41
              },
              "end": {
                "line": 11,
                "charByteOffset": 42
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "210": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "x",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 37
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 38
                }
              }
            },
            "twoStateIndex": "NEITHER"
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "5",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "5"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 41
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 42
                }
              }
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 11,
                "charByteOffset": 37
              },
              "end": {
                "line": 11,
                "charByteOffset": 42
              }
            },
            "hasParens": true
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Var.Full",
            "namePrefix": "I166",
            "tag": {
              "#class": "tac.Tag.Int"
            },
            "callIndex": 0,
            "meta": [
              {
                "key": {
                  "name": "cvl.type",
                  "type": "spec.cvlast.CVLType$PureCVLType",
                  "erasureStrategy": "CallTrace"
                },
                "value": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                  "k": 256
                }
              }
            ]
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.VariableExp",
            "id": "x",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                "k": 256
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 37
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 38
                }
              }
            },
            "twoStateIndex": "NEITHER"
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "5"
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
            "n": "5",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                "n": "5"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 41
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 42
                }
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "211": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.BinaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.RelopExp.EqExp",
          "l": {
            "#class": "spec.cvlast.CVLExp.FieldSelectExp",
            "structExp": {
              "#class": "spec.cvlast.CVLExp.ArrayDerefExp",
              "array": {
                "#class": "spec.cvlast.CVLExp.FieldSelectExp",
                "structExp": {
                  "#class": "spec.cvlast.CVLExp.VariableExp",
                  "id": "testContract",
                  "tag": {
                    "scope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        },
                        {
                          "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                          "scopeId": 9
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                          ],
                          "innerScope": null
                        }
                      }
                    },
                    "type": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract",
                      "name": {
                        "name": "TestContract"
                      }
                    },
                    "range": {
                      "#class": "utils.Range.Range",
                      "specFile": "test.spec",
                      "start": {
                        "line": 11,
                        "charByteOffset": 12
                      },
                      "end": {
                        "line": 11,
                        "charByteOffset": 24
                      }
                    },
                    "annotation": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId",
                      "instanceId": "ce4604a0000000000000000000000001"
                    }
                  },
                  "twoStateIndex": "NEITHER"
                },
                "fieldName": "m",
                "tag": {
                  "scope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      },
                      {
                        "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                        "scopeId": 9
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                        ],
                        "innerScope": null
                      }
                    }
                  },
                  "type": {
                    "#class": "spec.cvlast.CVLType.VM",
                    "descriptor": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor",
                      "keyType": {
                        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                        "bitwidth": 256
                      },
                      "valueType": {
                        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                        "canonicalId": "TestContract.sol|TestContract.Complex",
                        "location": null,
                        "fields": [
                          {
                            "fieldName": "s1",
                            "fieldType": {
                              "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                              "canonicalId": "TestContract.sol|TestContract.Simple",
                              "location": null,
                              "fields": [
                                {
                                  "fieldName": "x",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "y",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                  }
                                },
                                {
                                  "fieldName": "z1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "z2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "b1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                },
                                {
                                  "fieldName": "x2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "b2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                }
                              ],
                              "name": "TestContract.Simple"
                            }
                          },
                          {
                            "fieldName": "s2",
                            "fieldType": {
                              "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                              "canonicalId": "TestContract.sol|TestContract.Simple",
                              "location": null,
                              "fields": [
                                {
                                  "fieldName": "x",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "y",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                  }
                                },
                                {
                                  "fieldName": "z1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "z2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "b1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                },
                                {
                                  "fieldName": "x2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "b2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                }
                              ],
                              "name": "TestContract.Simple"
                            }
                          },
                          {
                            "fieldName": "b3",
                            "fieldType": {
                              "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                            }
                          }
                        ],
                        "name": "TestContract.Complex"
                      },
                      "location": null
                    },
                    "context": {
                      "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                    }
                  },
                  "range": {
                    "#class": "utils.Range.Range",
                    "specFile": "test.spec",
                    "start": {
                      "line": 11,
                      "charByteOffset": 12
                    },
                    "end": {
                      "line": 11,
                      "charByteOffset": 26
                    }
                  },
                  "annotation": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                  }
                }
              },
              "index": {
                "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
                "n": "0",
                "tag": {
                  "scope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      },
                      {
                        "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                        "scopeId": 9
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                        ],
                        "innerScope": null
                      }
                    }
                  },
                  "type": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                    "n": "0"
                  },
                  "range": {
                    "#class": "utils.Range.Range",
                    "specFile": "test.spec",
                    "start": {
                      "line": 11,
                      "charByteOffset": 27
                    },
                    "end": {
                      "line": 11,
                      "charByteOffset": 28
                    }
                  }
                }
              },
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.VM",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor",
                    "canonicalId": "TestContract.sol|TestContract.Complex",
                    "location": null,
                    "fields": [
                      {
                        "fieldName": "s1",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                          "canonicalId": "TestContract.sol|TestContract.Simple",
                          "location": null,
                          "fields": [
                            {
                              "fieldName": "x",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "y",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                              }
                            },
                            {
                              "fieldName": "z1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "z2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "b1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            },
                            {
                              "fieldName": "x2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "b2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            }
                          ],
                          "name": "TestContract.Simple"
                        }
                      },
                      {
                        "fieldName": "s2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                          "canonicalId": "TestContract.sol|TestContract.Simple",
                          "location": null,
                          "fields": [
                            {
                              "fieldName": "x",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "y",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                              }
                            },
                            {
                              "fieldName": "z1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "z2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "b1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            },
                            {
                              "fieldName": "x2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "b2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            }
                          ],
                          "name": "TestContract.Simple"
                        }
                      },
                      {
                        "fieldName": "b3",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                        }
                      }
                    ],
                    "name": "TestContract.Complex"
                  },
                  "context": {
                    "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                  }
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 11,
                    "charByteOffset": 12
                  },
                  "end": {
                    "line": 11,
                    "charByteOffset": 29
                  }
                },
                "annotation": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                }
              }
            },
            "fieldName": "b3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                }
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 32
                }
              },
              "annotation": {
                "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
              }
            }
          },
          "r": {
            "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
            "l": {
              "#class": "spec.cvlast.CVLExp.VariableExp",
              "id": "x",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                  "k": 256
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 11,
                    "charByteOffset": 37
                  },
                  "end": {
                    "line": 11,
                    "charByteOffset": 38
                  }
                }
              },
              "twoStateIndex": "NEITHER"
            },
            "r": {
              "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
              "n": "5",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                  "n": "5"
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 11,
                    "charByteOffset": 41
                  },
                  "end": {
                    "line": 11,
                    "charByteOffset": 42
                  }
                }
              }
            },
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 37
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 42
                }
              },
              "hasParens": true
            }
          },
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                  "scopeId": 9
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 11,
                "charByteOffset": 12
              },
              "end": {
                "line": 11,
                "charByteOffset": 43
              }
            }
          }
        },
        "o1": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "0",
            "tag": {
              "#class": "tac.Tag.Bool"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.FieldSelectExp",
            "structExp": {
              "#class": "spec.cvlast.CVLExp.ArrayDerefExp",
              "array": {
                "#class": "spec.cvlast.CVLExp.FieldSelectExp",
                "structExp": {
                  "#class": "spec.cvlast.CVLExp.VariableExp",
                  "id": "testContract",
                  "tag": {
                    "scope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        },
                        {
                          "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                          "scopeId": 9
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                          {
                            "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                          }
                        ],
                        "innerScope": {
                          "scopeStack": [
                          ],
                          "innerScope": null
                        }
                      }
                    },
                    "type": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.CodeContract",
                      "name": {
                        "name": "TestContract"
                      }
                    },
                    "range": {
                      "#class": "utils.Range.Range",
                      "specFile": "test.spec",
                      "start": {
                        "line": 11,
                        "charByteOffset": 12
                      },
                      "end": {
                        "line": 11,
                        "charByteOffset": 24
                      }
                    },
                    "annotation": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.CVLExp$VariableExp$ContractInstanceId",
                      "instanceId": "ce4604a0000000000000000000000001"
                    }
                  },
                  "twoStateIndex": "NEITHER"
                },
                "fieldName": "m",
                "tag": {
                  "scope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      },
                      {
                        "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                        "scopeId": 9
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                        ],
                        "innerScope": null
                      }
                    }
                  },
                  "type": {
                    "#class": "spec.cvlast.CVLType.VM",
                    "descriptor": {
                      "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMMappingDescriptor",
                      "keyType": {
                        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                        "bitwidth": 256
                      },
                      "valueType": {
                        "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                        "canonicalId": "TestContract.sol|TestContract.Complex",
                        "location": null,
                        "fields": [
                          {
                            "fieldName": "s1",
                            "fieldType": {
                              "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                              "canonicalId": "TestContract.sol|TestContract.Simple",
                              "location": null,
                              "fields": [
                                {
                                  "fieldName": "x",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "y",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                  }
                                },
                                {
                                  "fieldName": "z1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "z2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "b1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                },
                                {
                                  "fieldName": "x2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "b2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                }
                              ],
                              "name": "TestContract.Simple"
                            }
                          },
                          {
                            "fieldName": "s2",
                            "fieldType": {
                              "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                              "canonicalId": "TestContract.sol|TestContract.Simple",
                              "location": null,
                              "fields": [
                                {
                                  "fieldName": "x",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "y",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                                  }
                                },
                                {
                                  "fieldName": "z1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "z2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 8
                                  }
                                },
                                {
                                  "fieldName": "b1",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                },
                                {
                                  "fieldName": "x2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                    "bitwidth": 256
                                  }
                                },
                                {
                                  "fieldName": "b2",
                                  "fieldType": {
                                    "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                                  }
                                }
                              ],
                              "name": "TestContract.Simple"
                            }
                          },
                          {
                            "fieldName": "b3",
                            "fieldType": {
                              "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                            }
                          }
                        ],
                        "name": "TestContract.Complex"
                      },
                      "location": null
                    },
                    "context": {
                      "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                    }
                  },
                  "range": {
                    "#class": "utils.Range.Range",
                    "specFile": "test.spec",
                    "start": {
                      "line": 11,
                      "charByteOffset": 12
                    },
                    "end": {
                      "line": 11,
                      "charByteOffset": 26
                    }
                  },
                  "annotation": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                  }
                }
              },
              "index": {
                "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
                "n": "0",
                "tag": {
                  "scope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      },
                      {
                        "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                        "scopeId": 9
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                        {
                          "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                        }
                      ],
                      "innerScope": {
                        "scopeStack": [
                        ],
                        "innerScope": null
                      }
                    }
                  },
                  "type": {
                    "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                    "n": "0"
                  },
                  "range": {
                    "#class": "utils.Range.Range",
                    "specFile": "test.spec",
                    "start": {
                      "line": 11,
                      "charByteOffset": 27
                    },
                    "end": {
                      "line": 11,
                      "charByteOffset": 28
                    }
                  }
                }
              },
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.VM",
                  "descriptor": {
                    "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$EVMStructDescriptor",
                    "canonicalId": "TestContract.sol|TestContract.Complex",
                    "location": null,
                    "fields": [
                      {
                        "fieldName": "s1",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                          "canonicalId": "TestContract.sol|TestContract.Simple",
                          "location": null,
                          "fields": [
                            {
                              "fieldName": "x",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "y",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                              }
                            },
                            {
                              "fieldName": "z1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "z2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "b1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            },
                            {
                              "fieldName": "x2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "b2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            }
                          ],
                          "name": "TestContract.Simple"
                        }
                      },
                      {
                        "fieldName": "s2",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.EVMStructDescriptor",
                          "canonicalId": "TestContract.sol|TestContract.Simple",
                          "location": null,
                          "fields": [
                            {
                              "fieldName": "x",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "y",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.address"
                              }
                            },
                            {
                              "fieldName": "z1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "z2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 8
                              }
                            },
                            {
                              "fieldName": "b1",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            },
                            {
                              "fieldName": "x2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.UIntK",
                                "bitwidth": 256
                              }
                            },
                            {
                              "fieldName": "b2",
                              "fieldType": {
                                "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                              }
                            }
                          ],
                          "name": "TestContract.Simple"
                        }
                      },
                      {
                        "fieldName": "b3",
                        "fieldType": {
                          "#class": "spec.cvlast.typedescriptors.EVMTypeDescriptor.bool"
                        }
                      }
                    ],
                    "name": "TestContract.Complex"
                  },
                  "context": {
                    "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                  }
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 11,
                    "charByteOffset": 12
                  },
                  "end": {
                    "line": 11,
                    "charByteOffset": 29
                  }
                },
                "annotation": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
                }
              }
            },
            "fieldName": "b3",
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.VM",
                "descriptor": {
                  "#class": "ReflectivePolymorphicSerializer::spec.cvlast.typedescriptors.EVMTypeDescriptor$bool"
                },
                "context": {
                  "#class": "spec.cvlast.typedescriptors.FromVMContext.StateValue"
                }
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 12
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 32
                }
              },
              "annotation": {
                "#class": "ReflectivePolymorphicSerializer::spec.cvlast.StorageAccessMarker"
              }
            }
          }
        },
        "o2": {
          "out": {
            "#class": "vc.data.TACSymbol.Const",
            "value": "0",
            "tag": {
              "#class": "tac.Tag.Bool"
            }
          },
          "exp": {
            "#class": "spec.cvlast.CVLExp.RelopExp.ArithRelopExp.GtExp",
            "l": {
              "#class": "spec.cvlast.CVLExp.VariableExp",
              "id": "x",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.UIntK",
                  "k": 256
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 11,
                    "charByteOffset": 37
                  },
                  "end": {
                    "line": 11,
                    "charByteOffset": 38
                  }
                }
              },
              "twoStateIndex": "NEITHER"
            },
            "r": {
              "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
              "n": "5",
              "tag": {
                "scope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    },
                    {
                      "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                      "scopeId": 9
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                      {
                        "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                      }
                    ],
                    "innerScope": {
                      "scopeStack": [
                      ],
                      "innerScope": null
                    }
                  }
                },
                "type": {
                  "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                  "n": "5"
                },
                "range": {
                  "#class": "utils.Range.Range",
                  "specFile": "test.spec",
                  "start": {
                    "line": 11,
                    "charByteOffset": 41
                  },
                  "end": {
                    "line": 11,
                    "charByteOffset": 42
                  }
                }
              }
            },
            "tag": {
              "scope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  },
                  {
                    "#class": "spec.cvlast.CVLScope.Item.CVLFunctionScopeItem",
                    "scopeId": 9
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                    {
                      "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                    }
                  ],
                  "innerScope": {
                    "scopeStack": [
                    ],
                    "innerScope": null
                  }
                }
              },
              "type": {
                "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.Bool"
              },
              "range": {
                "#class": "utils.Range.Range",
                "specFile": "test.spec",
                "start": {
                  "line": 11,
                  "charByteOffset": 37
                },
                "end": {
                  "line": 11,
                  "charByteOffset": 42
                }
              },
              "hasParens": true
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 11,
          "charByteOffset": 4
        },
        "end": {
          "line": 11,
          "charByteOffset": 44
        }
      }
    }
  ],
  "212": [
    {
      "key": {
        "name": "tac.meta",
        "type": "vc.data.TACMetaInfo",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "source": 0,
        "begin": 319,
        "len": 77,
        "jumpType": "EXIT",
        "address": "ce4604a0000000000000000000000001",
        "sourceContext": {
          "indexToFilePath": {
            "0": "TestContract.sol"
          },
          "sourceDir": ".post_autofinders.0"
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 31,
          "charByteOffset": 4
        },
        "end": {
          "line": 31,
          "charByteOffset": 22
        }
      }
    }
  ],
  "213": [
    {
      "key": {
        "name": "cvl.label.start.id",
        "type": "java.lang.Integer",
        "erasureStrategy": "Canonical"
      },
      "value": 25
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 32
        }
      }
    }
  ],
  "214": [
    {
      "key": {
        "name": "cvl.exp",
        "type": "spec.CVLExpToTACExprMeta",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "spec.CVLExpToTACExprMeta.NullaryCVLExp",
        "exp": {
          "#class": "spec.cvlast.CVLExp.Constant.NumberLit",
          "n": "0",
          "tag": {
            "scope": {
              "scopeStack": [
                {
                  "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                },
                {
                  "#class": "spec.cvlast.CVLScope.Item.RuleScopeItem",
                  "scopeId": 3
                }
              ],
              "innerScope": {
                "scopeStack": [
                  {
                    "#class": "spec.cvlast.CVLScope.Item.AstScopeItem"
                  }
                ],
                "innerScope": {
                  "scopeStack": [
                  ],
                  "innerScope": null
                }
              }
            },
            "type": {
              "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
              "n": "0"
            },
            "range": {
              "#class": "utils.Range.Range",
              "specFile": "test.spec",
              "start": {
                "line": 33,
                "charByteOffset": 26
              },
              "end": {
                "line": 33,
                "charByteOffset": 27
              }
            }
          }
        }
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 32
        }
      }
    }
  ],
  "215": [
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 32
        }
      }
    }
  ],
  "216": [
    {
      "key": {
        "name": "tac.direct.storage.access",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 32
        }
      }
    }
  ],
  "217": [
    {
      "key": {
        "name": "tac.is-temp-var",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "tac.storage.access-paths",
        "type": "analysis.storage.StorageAnalysisResult$AccessPaths",
        "erasureStrategy": "Canonical"
      },
      "value": {
        "paths": [
          {
            "#class": "analysis.storage.StorageAnalysis.AnalysisPath.StructAccess",
            "base": {
              "#class": "analysis.storage.StorageAnalysis.AnalysisPath.MapAccess",
              "base": {
                "#class": "analysis.storage.StorageAnalysis.AnalysisPath.Root",
                "slot": "0"
              },
              "key": {
                "#class": "vc.data.TACSymbol.Var.Full",
                "namePrefix": "I171",
                "tag": {
                  "#class": "tac.Tag.Int"
                },
                "callIndex": 0,
                "meta": [
                  {
                    "key": {
                      "name": "cvl.type",
                      "type": "spec.cvlast.CVLType$PureCVLType",
                      "erasureStrategy": "CallTrace"
                    },
                    "value": {
                      "#class": "spec.cvlast.CVLType.PureCVLType.Primitive.NumberLiteral",
                      "n": "0"
                    }
                  }
                ]
              },
              "baseSlot": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              },
              "hashResult": {
                "#class": "vc.data.TACSymbol.Const",
                "value": "0"
              }
            },
            "offset": {
              "#class": "analysis.storage.StorageAnalysis.Offset.Bytes",
              "numBytes": "100"
            }
          }
        ]
      }
    }
  ],
  "218": [
    {
      "key": {
        "name": "cvl.user.defined.assert",
        "type": "tac.MetaMap$Companion$NothingValue",
        "erasureStrategy": "Canonical"
      },
      "value": {
      }
    },
    {
      "key": {
        "name": "cvl.range",
        "type": "utils.Range",
        "erasureStrategy": "CallTrace"
      },
      "value": {
        "#class": "utils.Range.Range",
        "specFile": "test.spec",
        "start": {
          "line": 33,
          "charByteOffset": 4
        },
        "end": {
          "line": 33,
          "charByteOffset": 32
        }
      }
    }
  ]
}
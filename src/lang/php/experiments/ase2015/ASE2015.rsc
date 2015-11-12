module lang::php::experiments::ase2015::ASE2015

import lang::php::ast::AbstractSyntax;
import lang::php::util::Config;
import lang::php::util::Utils;
import lang::php::util::Corpus;
import lang::php::ast::System;
import lang::php::stats::Stats;
import lang::php::analysis::includes::IncludeGraph;
import lang::php::analysis::includes::IncludesInfo;
import lang::php::analysis::includes::QuickResolve;
import lang::php::analysis::includes::ScriptResolve;
import lang::php::analysis::includes::LibraryIncludes;
import lang::php::stats::Unfriendly;
import lang::php::pp::PrettyPrinter;
import lang::php::analysis::cfg::CFG;
import lang::php::analysis::cfg::Util;
import lang::php::analysis::cfg::BuildCFG;
import lang::php::analysis::NamePaths;
import lang::php::analysis::evaluators::AlgebraicSimplification;
import lang::php::analysis::names::AnalysisNames;
import lang::php::analysis::signatures::Summaries;
import lang::php::analysis::signatures::Signatures;
import lang::php::analysis::evaluators::SimulateCalls;

import Set;
import List;
import String;
import ValueIO;
import DateTime;
import util::Math;
import Node;
import Relation;
import Map;
import util::Maybe;
import Traversal;
import IO;

//
// NOTES
//
// 1. The hasDangerousUse

@doc{The base corpus used in the ASE 2015 submission.}
private Corpus ase15BaseCorpus = (
	"osCommerce":"2.3.4",
	"ZendFramework":"2.3.7",
	"CodeIgniter":"3.0.0",
	"Symfony":"2.6.5",
	"SilverStripe":"3.1.2",
	"WordPress":"4.1.1",
	"Joomla":"3.4.1",
	"phpBB":"3.1.3",
	"Drupal":"7.35",
	"MediaWiki":"1.24.1",
	"Gallery":"3.0.9",
	"SquirrelMail":"1.4.22",
	"Moodle":"2.8.5",
	"Smarty":"3.1.21",
	"Kohana":"3.3.3.1",
	"phpMyAdmin":"4.3.13-english",
	"PEAR":"1.9.5",
	"CakePHP":"2.6.3", // may want to check 3.0 as well
	"DoctrineORM":"2.4.7",
	"Magento":"1.9.1.0");

@doc{Retrieve the base corpus}
public Corpus getBaseCorpus() = ase15BaseCorpus;

@doc{Build the corpus files.}
public void buildCorpus(Corpus corpus, bool overwrite=false) {
	for (p <- corpus, v := corpus[p]) {
		buildBinaries(p,v,overwrite=overwrite);
	}
}

@doc{Build the base corpus.}
public void buildCorpus() {
	buildCorpus(getBaseCorpus());
}

public str showVVInfoAsLatex(list[tuple[str p, str v, QueryResult qr]] vvuses, 
				 		   	 list[tuple[str p, str v, QueryResult qr]] vvcalls,
							 list[tuple[str p, str v, QueryResult qr]] vvmcalls,
							 list[tuple[str p, str v, QueryResult qr]] vvnews,
							 list[tuple[str p, str v, QueryResult qr]] vvprops,
							 list[tuple[str p, str v, QueryResult qr]] vvall,
							 Corpus corpus) {
							 
	ci = loadCountsCSV();
	hasGini = ( p : (size({qr|<p,_,qr> <- vvall}) > 1) ? true : false | p <- corpus );
	
	gmap = resultsToGini(vvall);
	
	str headerLine() {
		return "Product & Files & \\multicolumn{18}{c}{PHP Variable Features} \\\\
		       '\\cmidrule{3-20}
		       ' & & \\multicolumn{2}{c}{Variables} & \\phantom{a} & \\multicolumn{2}{c}{Function Calls} & \\phantom{a} & \\multicolumn{2}{c}{Method Calls} & \\phantom{a} & \\multicolumn{2}{c}{Property Fetches} & \\phantom{a} & \\multicolumn{2}{c}{Instantiations} & \\phantom{a} & \\multicolumn{3}{c}{All} \\\\
		       '\\cmidrule{3-4} \\cmidrule{6-7} \\cmidrule{9-10} \\cmidrule{12-13} \\cmidrule{15-16} \\cmidrule{18-20}
		       ' &  & Files & Uses && Files & Uses && Files & Uses && Files & Uses && Files & Uses && Files & Uses & Gini \\\\ \\midrule";
	}
	
	str c(str p, list[tuple[str p, str v, QueryResult qr]] vv) = "\\numprint{<size({qr.l.path|<p,_,qr><-vv})>} & \\numprint{<size([qr|<p,_,qr><-vv])>}";
	
	str productLine(str p) {
		< lineCount, fileCount > = getOneFrom(ci[p,corpus[p]]);
		return "<p> & \\numprint{<fileCount>} & <c(p,vvuses)> && <c(p,vvcalls)> && <c(p,vvmcalls)> && <c(p,vvprops)> && <c(p,vvnews)> && \\numprint{<size({qr.l.path|<p,_,qr><-vvall})>} & \\numprint{<size([qr|<p,_,qr><-vvall])>} & < (!hasGini[p]) ? "N/A" : "\\nprounddigits{2} \\numprint{<round(gmap[p] * 100.0)/100.0>} \\npnoround" > \\\\";
	}

	res = "\\npaddmissingzero
		  '\\npfourdigitsep
		  '\\begin{table*}
		  '\\centering
		  '\\ra{1.0}
		  '\\resizebox{\\textwidth}{!}{%
		  '\\begin{tabular}{@{}lrrrcrrcrrcrrcrrcrrr@{}} \\toprule 
		  '<headerLine()> <for (p <- sort(toList(corpus<0>),bool(str s1,str s2) { return toUpperCase(s1)<toUpperCase(s2); })) {>
		  '  <productLine(p)> <}>
		  '\\bottomrule
		  '\\end{tabular}
		  '}
		  '\\caption{PHP Variable Features.\\label{table-var}}
		  '\\end{table*}
		  '";
	return res;
}

public str generateVVTable() {
	ase = getBaseCorpus();
	//ase = domainR(ase, {"phpBB"});
	< vvuses, vvcalls, vvmcalls, vvnews, vvprops, vvcconsts, vvscalls, vvstargets, vvsprops, vvsptargets > = getAllVV(ase);
	return showVVInfoAsLatex(vvuses, vvcalls, vvmcalls, vvnews, vvprops,
		vvuses + vvcalls + vvmcalls + vvnews + vvprops + vvcconsts + vvscalls +
		vvstargets + vvsprops + vvsptargets, ase);
}

public void runAnalysis(System sys) {
	fetches = gatherPropertyFetchesWithVarNames(sys);
	vars = gatherVarVarUses(sys);
}

data CFG = emptyCFG();

public CFG cfgForLocation(map[NamePath,CFG] cfgs, loc l) {
	cfgsFound = { c | c <- cfgs<1>, /Expr e2 := c, (e2@at)?, e2@at == l};
	if (size(cfgsFound) > 0) {
		return getOneFrom(cfgsFound);
	}
	return emptyCFG();
}

public CFG cfgForExpression(map[NamePath,CFG] cfgs, Expr e) {
	return cfgForLocation(cfgs, e@at);
}

public bool hasVariableForName(var(expr(var(name(name(str s)))))) = true; // Variable variable
public bool hasVariableForName(call(expr(var(name(name(str s)))),_)) = true; // Variable function
public bool hasVariableForName(methodCall(_,expr(var(name(name(str s)))),_)) = true; // Variable method
public bool hasVariableForName(new(expr(var(name(name(str s)))),_)) = true; // Variable new
public bool hasVariableForName(propertyFetch(_,expr(var(name(name(str s)))))) = true; // Variable property
public bool hasVariableForName(staticCall(_,expr(var(name(name(str s)))),_)) = true; // Variable static call
public bool hasVariableForName(staticCall(expr(var(name(name(str s)))),_,_)) = true; // Variable static target
public bool hasVariableForName(staticPropertyFetch(expr(var(name(name(str s)))),_)) = true;
public bool hasVariableForName(staticPropertyFetch(_,expr(var(name(name(str s)))))) = true;
public bool hasVariableForName(fetchClassConst(expr(var(name(name(str s)))),_)) = true;
public default bool hasVariableForName(Expr e) = false;

public str getVariableName(var(expr(var(name(name(str s)))))) = s;
public str getVariableName(call(expr(var(name(name(str s)))),_)) = s;
public str getVariableName(methodCall(_,expr(var(name(name(str s)))),_)) = s;
public str getVariableName(new(expr(var(name(name(str s)))),_)) = s;
public str getVariableName(propertyFetch(_,expr(var(name(name(str s)))))) = s;
public str getVariableName(staticCall(_,expr(var(name(name(str s)))),_)) = s;
public str getVariableName(staticCall(expr(var(name(name(str s)))),_,_)) = s;
public str getVariableName(staticPropertyFetch(expr(var(name(name(str s)))),_)) = s;
public str getVariableName(staticPropertyFetch(_,expr(var(name(name(str s)))))) = s;
public str getVariableName(fetchClassConst(expr(var(name(name(str s)))),_)) = s;
public default str getVariableName(Expr e) { 
	throw "No variable name found"; 
}

public Expr getVariablePart(var(expr(Expr e))) = e;
public Expr getVariablePart(call(expr(Expr e),_)) = e;
public Expr getVariablePart(methodCall(_,expr(Expr e),_)) = e;
public Expr getVariablePart(new(expr(Expr e),_)) = e;
public Expr getVariablePart(propertyFetch(_,expr(Expr e))) = e;
public Expr getVariablePart(staticCall(_,expr(Expr e),_)) = e;
public Expr getVariablePart(staticCall(expr(Expr e),_,_)) = e;
public Expr getVariablePart(staticPropertyFetch(expr(Expr e),_)) = e;
public Expr getVariablePart(staticPropertyFetch(_,expr(Expr e))) = e;
public Expr getVariablePart(fetchClassConst(expr(Expr e),_)) = e;
public default Expr getVariablePart(Expr e) { 
	throw "No variable name found"; 
}

public bool exprIsScalar(Expr e) {
	e = algebraicSimplification(e);
	return (scalar(s) := e && encapsed(_) !:= s);
}

public bool exprIsScalarString(Expr e) {
	solve(e) {
		e = bottom-up visit(e) {
			case Expr e2 => simulateCall(algebraicSimplification(e2))
		}
	}
	return (scalar(string(s)) := e);
}

public bool exprIsScalarStringOrChained(Expr e, bool reduce=true) {
	if (reduce) {
		solve(e) {
			e = bottom-up visit(e) {
				case Expr e2 => simulateCall(algebraicSimplification(e2))
			}
		}
	}
	return (scalar(string(s)) := e || (assign(_,e2) := e && exprIsScalarString(e2,reduce=false)));
}

public bool exprIsArrayOfStringsOrChained(Expr e, bool reduce=true) {
	if (reduce) {
		solve(e) {
			e = bottom-up visit(e) {
				case Expr e2 => simulateCall(algebraicSimplification(e2))
			}
		}
	}
	return (( array(el) := e && false notin { scalar(string(_)) := av | arrayElement(_,av,_) <- el } ) || (assign(_,e2) := e && exprIsArrayOfStringsOrChained(e2,reduce=false)));
}

public str getScalarString(Expr e) {
	solve(e) {
		e = bottom-up visit(e) {
			case Expr e2 => simulateCall(algebraicSimplification(e2))
		}
	}

	if (scalar(string(s)) := e) {
		return s;
	}
	throw "No value";
}

public str getScalarStringOrChained(Expr e, bool reduce=true) {
	if (reduce) {
		solve(e) {
			e = bottom-up visit(e) {
				case Expr e2 => simulateCall(algebraicSimplification(e2))
			}
		}
	}
	if (scalar(string(s)) := e) {
		return s;
	} else if (assign(_,e2) := e) {
		return getScalarString(e2,reduce=false);
	}
	throw "No value";
}

public set[str] getArrayOfStringsOrChained(Expr e, bool reduce=true) {
	if (reduce) {
		solve(e) {
			e = bottom-up visit(e) {
				case Expr e2 => simulateCall(algebraicSimplification(e2))
			}
		}
	}
	if (array(el) := e) {
		return { v | arrayElement(_,scalar(string(v)),_) <- el };
	} else if (assign(_,e2) := e) {
		return getScalarString(e2,reduce=false);
	}
	throw "No value";
}

public set[str] gatherAssignedStrings(CFG g, Expr e) {
	return { getScalarString(e2) | exprNode(assign(e, e2),_) <- g.nodes, exprIsScalarString(e2) };
}

public set[str] gatherAssignedStringsWithChaining(CFG g, Expr e) {
	return { getScalarStringOrChained(e2) | exprNode(assign(e, e2),_) <- g.nodes, exprIsScalarStringOrChained(e2) };
}

public set[str] gatherArrayOfStringsWithChaining(CFG g, Expr e) {
	return { *getArrayOfStringsOrChained(e2) | exprNode(assign(e, e2),_) <- g.nodes, exprIsArrayOfStringsOrChained(e2) };
}

public bool ternaryHasStringResults(Expr e) {
	if (ternary(_,someExpr(e2),e3) := e) {
		e2res = (e2 is ternary) ? ternaryHasStringResults(e2) : (scalar(string(_)) := e2);
		e3res = (e3 is ternary) ? ternaryHasStringResults(e3) : (scalar(string(_)) := e3);
		return e2res && e3res;
	}
	return false;
}

public set[str] ternaryStringResults(Expr e) {
	res = { };
	if (e.ifBranch.expr is ternary) {
		res = ternaryStringResults(e.ifBranch.expr);
	} else {
		res = { e.ifBranch.expr.scalarVal.strVal };
	}
	if (e.elseBranch is ternary) {
		res = res + ternaryStringResults(e.elseBranch);
	} else {
		res = res + { e.elseBranch.scalarVal.strVal };
	}
	return res;
}


public set[str] gatherAssignedStrings2(CFG g, Expr e) {
	set[str] res = { };
	if (exprNode(assign(e, e2),_) <- g.nodes) {
		e2 = algebraicSimplification(e2);
		if (e2 is ternary) {
			res = ternaryStringResults(e2);
		}
	}
	
	return res;
}

set[QueryResult] collapseVVInfo(VVInfo vv) {
	return toSet(vv.vvuses<2> + vv.vvcalls<2> + vv.vvmcalls<2> + vv.vvnews<2> + vv.vvprops<2> + vv.vvcconsts<2> + vv.vvscalls<2> +
		vv.vvstargets<2> + vv.vvsprops<2> + vv.vvsptargets<2>);
}

data ResolveStats = resolveStats(int resolved, rel[loc,AnalysisName] resolvedLocs, set[loc] unresolvedLocs);

public ResolveStats addResolveStats(ResolveStats r1, ResolveStats r2, bool fixUnresolved = true) {
	r1.resolved = r1.resolved + r2.resolved;
	r1.resolvedLocs = r1.resolvedLocs + r2.resolvedLocs;
	r1.unresolvedLocs = r1.unresolvedLocs + r2.unresolvedLocs;
	if (fixUnresolved) {
		r1.unresolvedLocs = r1.unresolvedLocs - (r1.resolvedLocs<0> + r2.resolvedLocs<0>);
	}
	return r1;
}

data PatternStats = patternStats(ResolveStats vvuses, ResolveStats vvcalls, ResolveStats vvmcalls, ResolveStats vvnews, ResolveStats vvprops,
								 ResolveStats vvcconsts, ResolveStats vvscalls, ResolveStats vvstargets, ResolveStats vvsprops, ResolveStats vvsptargets);

public PatternStats addPatternStats(PatternStats p1, PatternStats p2, bool fixUnresolved = true) {
	return patternStats(addResolveStats(p1.vvuses, p2.vvuses, fixUnresolved = fixUnresolved), 
						addResolveStats(p1.vvcalls, p2.vvcalls, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvmcalls, p2.vvmcalls, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvnews, p2.vvnews, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvprops, p2.vvprops, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvcconsts, p2.vvcconsts, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvscalls, p2.vvscalls, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvstargets, p2.vvstargets, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvsprops, p2.vvsprops, fixUnresolved = fixUnresolved),
						addResolveStats(p1.vvsptargets, p2.vvsptargets, fixUnresolved = fixUnresolved));
}

//public ResolveStats fixResolveStats(ResolveStats rs, set[loc] resolved) {
//	rs.unresolvedLocs = rs.unresolvedLocs - resolved;
//	return rs; 
//}

public map[str s, PatternStats p] addPatternStats(map[str s, PatternStats p] p1, map[str s, PatternStats p] p2, bool fixUnresolved = true) {
	return (s : addPatternStats(p1[s], p2[s], fixUnresolved = fixUnresolved) | s <- p1 );
}


//public PatternStats fixPatternStats(PatternStats p1, set[loc] resolved) {
//	return patternStats(fixResolveStats(p1.vvuses, resolved), fixResolveStats(p1.vvcalls, resolved),
//						fixResolveStats(p1.vvmcalls, resolved), fixResolveStats(p1.vvnews, resolved),
//						fixResolveStats(p1.vvprops, resolved), fixResolveStats(p1.vvcconsts, resolved),
//						fixResolveStats(p1.vvscalls, resolved), fixResolveStats(p1.vvstargets, resolved),
//						fixResolveStats(p1.vvsprops, resolved), fixResolveStats(p1.vvsptargets, resolved));
//}
//
//public map[str s, PatternStats p] fixPatternStats(map[str s, PatternStats p] p1, map[str s, set[loc] resolved] resolvedMap) {
//	return (s : fixPatternStats(p1[s],resolvedMap[s]) | s <- p1 );
//}


public bool hasDangerousUse(Stmt s, str v, FMParamInfo fm, set[loc] ignoreLocs = { }, bool ignoreNormalAssign=false) {
	visit(s) {
		case du:assign(var(name(name(v))),_) : {
			if (du@at notin ignoreLocs || ignoreNormalAssign) {
				println("Dangerous use found at <du@at>: <pp(du)>");
				return true;
			}
		}

		case du:assignWOp(var(name(name(v))),_,_) : {
			if (du@at notin ignoreLocs) {
				println("Dangerous use found at <du@at>: <pp(du)>");
				return true;
			}
		}

		case du:listAssign([_*,someExpr(var(name(name(v)))),_*],_) : {
			if (du@at notin ignoreLocs) {
				println("Dangerous use found at <du@at>: <pp(du)>");
				return true;
			}
		}
		
		case du:refAssign(var(name(name(v))),_) : {
			if (du@at notin ignoreLocs) {
				println("Dangerous use found at <du@at>: <pp(du)>");
				return true;
			}
		}
		
		case du:call(ct,plist) : {
			if (du@at notin ignoreLocs) {
				if (name(name(fn)) := ct) {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						if (fn in fm.functions<0>) {
							fnMatches = fm.functions[fn];
							for (fnMatch <- fnMatches, size(fnMatch) >= (idx+1), fnMatch[idx].isRef) {
								println("Dangerous use, used as reference parameter at <du@at>: <pp(du)>");
								return true;
							}
						} else {
							println("Dangerous use, unknown function call, found at <du@at>: <pp(du)>");
							return true;
						}
					}
				} else {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						// This ensures we only treat this as a dangerous call if the variable name we
						// are checking against is used as a parameter.
						println("Dangerous use, variable function call, found at <du@at>: <pp(du)>");
						return true;
					}
				}
			}
		}

		case du:methodCall(_,mt,plist) : {
			if (du@at notin ignoreLocs) {
				if (name(name(mn)) := mt) {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						if (mn in fm.methods<0>) {
							mnMatches = fm.methods[mn];
							for (mnMatch <- mnMatches, size(mnMatch) >= (idx+1), mnMatch[idx].isRef) {
								println("Dangerous use, used as reference parameter at <du@at>: <pp(du)>");
								return true;
							}
						} else {
							println("Dangerous use, unknown method found at <du@at>: <pp(du)>");
							return true;
						}
					}
				} else {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						// This ensures we only treat this as a dangerous call if the variable name we
						// are checking against is used as a parameter.
						println("Dangerous use, variable method call, found at <du@at>: <pp(du)>");
						return true;
					}
				}
			}
		}

		case du:staticCall(_,mt,plist) : {
			if (du@at notin ignoreLocs) {
				if (name(name(mn)) := mt) {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						if (mn in fm.methods<0>) {
							mnMatches = fm.methods[mn];
							for (mnMatch <- mnMatches, size(mnMatch) >= (idx+1), mnMatch[idx].isRef) {
								println("Dangerous use, used as reference parameter at <du@at>: <pp(du)>");
								return true;
							}
						} else {
							println("Dangerous use, unknown static method found at <du@at>: <pp(du)>");
							return true;
						}
					}
				} else {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						// This ensures we only treat this as a dangerous call if the variable name we
						// are checking against is used as a parameter.
						println("Dangerous use, variable static method call, found at <du@at>: <pp(du)>");
						return true;
					}
				}
			}
		}
	}
	
	return false;
}

public bool addressTaken(CFG g, str v, FMParamInfo fm, set[loc] ignoreLocs = { }, bool must = true) {
	for (exprNode(e,_) <- g.nodes) {
		switch(e) {
			case du:refAssign(var(name(name(v))),_) : {
				if (du@at notin ignoreLocs) {
					println("Address taken, reference assignment at <du@at>: <pp(du)>");
					return true;
				}
			}
			
			case du:call(ct,plist) : {
				if (du@at notin ignoreLocs) {
					if (name(name(fn)) := ct) {
						for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
							if (fn in fm.functions<0>) {
								fnMatches = fm.functions[fn];
								for (fnMatch <- fnMatches, size(fnMatch) >= (idx+1), fnMatch[idx].isRef) {
									println("Address taken, used with reference parameter at <du@at>: <pp(du)>");
									return true;
								}
							} else if (!must) {
								println("Address possibly taken, unknown function found at <du@at>: <pp(du)>");
								return true;
							}
						}
					} else if (!must) {
						println("Address possibly taken, unknown call, found at <du@at>: <pp(du)>");
						return true;
					}
				}
			}
	
			case du:methodCall(_,mt,plist) : {
				if (du@at notin ignoreLocs) {
					if (name(name(mn)) := mt) {
						for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
							if (mn in fm.methods<0>) {
								mnMatches = fm.methods[mn];
								for (mnMatch <- mnMatches, size(mnMatch) >= (idx+1), mnMatch[idx].isRef) {
									println("Address taken, used with reference parameter at <du@at>: <pp(du)>");
									return true;
								}
							} else if (!must) {
								println("Address possibly taken, unknown function found at <du@at>: <pp(du)>");
								return true;
							}
						}
					} else if (!must) {
						println("Address possibly taken, unknown call, found at <du@at>: <pp(du)>");
						return true;
					}
				}
			}
	
			case du:staticCall(_,mt,plist) : {
				if (du@at notin ignoreLocs) {
					if (name(name(mn)) := mt) {
						for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
							if (mn in fm.methods<0>) {
								mnMatches = fm.methods[mn];
								for (mnMatch <- mnMatches, size(mnMatch) >= (idx+1), mnMatch[idx].isRef) {
									println("Address taken, used with reference parameter at <du@at>: <pp(du)>");
									return true;
								}
							} else if (!must) {
								println("Address possibly taken, unknown function found at <du@at>: <pp(du)>");
								return true;
							}
						}
					} else if (!must) {
						println("Address possibly taken, unknown call, found at <du@at>: <pp(du)>");
						return true;
					}
				}
			}
		}
	}
	
	return false;
}

@doc{
	Resolve variable definitions for Pattern One. Pattern one is the following:
	
	1. A foreach loop is defined that works directly over a literal array
	2. Each element of this array is assigned into the foreach variable representing the value
	3. This foreach variable is used directly as the name of the variable being accessed

	TODO: Add example here
	
	We can resolve this under the restriction that the foreach variable is not used
	in a way where it could be modified (it is not passed to a function or method
	as a reference parameter, it is not reference assigned to another variable, it
	is not used as the target of an assignment). This also needs to occur in the
	context of the foreach that provides the variable.
}
public rel[loc,AnalysisName] loopPatternOne(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats loopPatternOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Get variable features that are not yet resolved
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-1 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getVariableName(e);
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-1: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (array(aelist) := aexp && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
							// NOTE: This is only checking inside the foreach loop, not in the surrounding code; check inside the containing unit instead...
							if (hasDangerousUse(fe, v, fm)) {
								println("LP-1: Cannot use foreach, it has a potentially dangerous use, <fe@at>");
								unres = unres + qr.l;
							} else if (addressTaken(c, v, fm)) {
								println("LP-1: Cannot use variable, its address is potentially taken, <v>");
								unres = unres + qr.l;
							} else {
								res = res + { < qr.l, varName(getScalarString(aeItem.val)) > | aeItem <- aelist };
							}
						} else {
							println("LP-1: Array expression <pp(aexp)> does not match pattern 1, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternOne(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternOne(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("one"),s));
	}
	
	return res;
}

rel[loc,Expr] getStandardAssignmentsFor(str varname, set[CFGNode] nodes) {
	return { < e@at, e > | exprNode(e:assign(var(name(name(varname))),_),_) <- nodes };
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is the following:
	
	1. A literal array is defined and assigned to a variable
	2. A foreach loop is defined that works over this variable
	3. Each element of this array is assigned into the foreach variable representing the value
	4. This foreach variable is used directly as the name of the variable being accessed
	
	TODO: Add example

	We can resolve this under the restriction that the foreach variable is not used
	in a way where it could be modified (it is not passed to a function or method
	as a reference parameter, it is not reference assigned to another variable, it
	is not used as the target of an assignment). This also needs to occur in the
	context of the foreach that provides the variable.
}
public rel[loc,AnalysisName] loopPatternTwo(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternTwo(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternTwo(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-2 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getVariableName(e);
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-2: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
							// TODO: Verify reachability, currently we are assuming this assignment reaches this use
							//assignments = getStandardAssignmentsFor(aname, carrier(g));
							assignments = reachingDefs(c, aname, qr.e);
							if (size(assignments<1>) == 1) {
								assignLocs = assignments<0>;
								assignExpr = getOneFrom(assignments<1>);						
								if (array(aelist) := assignExpr.assignExpr && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
									if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
										println("LP-2: Cannot use foreach, it has a potentially dangerous use");
										unres = unres + qr.l;
									} else if (addressTaken(c, v, fm)) {
										println("LP-2: Cannot use variable, its address is potentially taken, <v>");
										unres = unres + qr.l;
									} else {
										res = res + { < qr.l, varName(getScalarString(aeItem.val)) > | aeItem <- aelist };
									}
								} else {
									println("LP-2: Array expression <pp(aexp)> at <aexp@at> does not match pattern 2, <qr.l>");
									unres = unres + qr.l;
								}
							} else if (isEmpty(assignments<1>)) {
								println("LP-2: No local assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							} else {
								println("LP-2: Inconsistent assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							}							
						} else {
							println("LP-2: Array expression in foreach <pp(aexp)> does not match pattern 2, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternTwo(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternTwo(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("two"),s));
	}
	
	return res;
}


@doc{
	Resolve variable definitions for Pattern Three. Pattern three is identical to pattern
	one except here we use the key in the foreach, not the standard foreach variable (e.g.,
	we have $key => $value and use $key, not $value).

	TODO: Add example
}

public rel[loc,AnalysisName] loopPatternThree(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternThree(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats loopPatternThree(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Get variable features that are not yet resolved
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-3 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {			
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getVariableName(e);
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,someExpr(var(name(name(v)))),_,_,_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-3: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (array(aelist) := aexp && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {
							if (hasDangerousUse(fe, v, fm)) {
								println("LP-3: Cannot use foreach, it has a potentially dangerous use, <fe@at>");
								unres = unres + qr.l;
							} else if (addressTaken(c, v, fm)) {
								println("LP-3: Cannot use variable, its address is potentially taken, <v>");
								unres = unres + qr.l;
							} else {
								res = res + { < qr.l, varName(getScalarString(aeItem.key.expr)) > | aeItem <- aelist };
							}
						} else {
							println("LP-3: Array expression <pp(aexp)> does not match pattern 3, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternThree(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternThree(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("three"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Four. Pattern four is identical to pattern
	two except here we use the key in the foreach, not the standard foreach variable (e.g.,
	we have $key => $value and use $key, not $value).

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternFour(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternFour(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternFour(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-4 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getVariableName(e);
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,someExpr(var(name(name(v)))),_,_,_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-4: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
							// TODO: Verify reachability
							//assignments = getStandardAssignmentsFor(aname, carrier(g));
							assignments = reachingDefs(c, aname, qr.e);
							if (size(assignments<1>) == 1) {
								assignLocs = assignments<0>;
								assignExpr = getOneFrom(assignments<1>);			
								if (array(aelist) := assignExpr.assignExpr && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {			
									if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
										println("LP-4: Cannot use foreach, it has a potentially dangerous use");
										unres = unres + qr.l;
									} else if (addressTaken(c, v, fm)) {
										println("LP-4: Cannot use variable, its address is potentially taken, <v>");
										unres = unres + qr.l;
									} else {
										res = res + { < qr.l, varName(getScalarString(aeItem.key.expr)) > | aeItem <- aelist };
									}
								} else {
									println("LP-4: Array expression <pp(aexp)> at <aexp@at> does not match pattern 4, <qr.l>");
									unres = unres + qr.l;
								}
							} else if (isEmpty(assignments<1>)) {
								println("LP-4: No local assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							} else {
								println("LP-4: Inconsistent assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							}							
						} else {
							println("LP-4: Array expression in foreach <pp(aexp)> does not match pattern 4, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternFour(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternFour(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("four"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Five. Pattern five is very similar to pattern one, but in this
	case, instead of using the foreach variable as the name of the variable to look up, we have a second
	variable which is assigned a string value that includes the foreach variable. This second variable is
	then used to determine the identifier.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternFive(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternFive(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternFive(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-5 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case Expr e2 : {
							if ((e2@at)? && (e2@at == qr.l)) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("LP-5: Cannot use foreach, it creates an alias, <fe@at>");
							unres = unres + qr.l;
						} else {
							aexp = fe.arrayExpr;
							if (array(aelist) := aexp && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
								if (hasDangerousUse(fe, v, fm)) {
									println("LP-5: Cannot use foreach, it has a potentially dangerous use");
									unres = unres + qr.l;
								} else if (addressTaken(c, v, fm)) {
									println("LP-5: Cannot use variable, its address is potentially taken, <v>");
									unres = unres + qr.l;
								} else {
									varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.val | aeItem <- aelist }); 
									res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
								}
							} else {
								println("LP-5: Array expression <pp(aexp)> at <aexp@at> does not match pattern 5, <qr.l>");
								unres = unres + qr.l;
							}
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternFive(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternFive(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("five"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Six. Pattern six is very similar to pattern two, but in this
	case, instead of using the foreach variable as the name of the variable to look up, we have a second
	variable which is assigned a string value that includes the foreach variable. This second variable is
	then used to determine the identifier.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternSix(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternSix(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternSix(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-6 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case Expr e2 : {
							if ((e2@at)? && (e2@at == qr.l)) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("LP-6: Cannot use foreach, it creates an alias, <fe@at>");
							unres = unres + qr.l;
						} else {
							aexp = fe.arrayExpr;
							if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
								// TODO: Verify reachability
								//assignments = getStandardAssignmentsFor(aname, carrier(g));
								assignments = reachingDefs(c, aname, qr.e);
								if (size(assignments<1>) == 1) {
									assignLocs = assignments<0>;
									assignExpr = getOneFrom(assignments<1>);						
									if (array(aelist) := assignExpr.assignExpr && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
										if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
											println("LP-6: Cannot use foreach, it has a potentially dangerous use");
											unres = unres + qr.l;
										} else if (addressTaken(c, v, fm)) {
											println("LP-6: Cannot use variable, its address is potentially taken, <v>");
											unres = unres + qr.l;
										} else {
											varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.val | aeItem <- aelist }); 
											res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
										}
									} else {
										println("LP-6: Array expression <pp(aexp)> at <aexp@at> does not match pattern 6, <qr.l>");
										unres = unres + qr.l;
									}
								} else if (isEmpty(assignments<1>)) {
									println("LP-6: No local assignments, cannot use variable <aname>, <qr.l>");
									unres = unres + qr.l;
								} else {
									println("LP-6: Inconsistent assignments, cannot use variable <aname>, <qr.l>");
									unres = unres + qr.l;
								}							
							} else {
								println("LP-6: Array expression in foreach <pp(aexp)> does not match pattern 8, <qr.l>");
								unres = unres + qr.l;
							}
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternSix(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternSix(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("six"),s));
	}
	
	return res;
}


@doc{
	Resolve variable definitions for Pattern Seven. Pattern seven is very similar to pattern three, but in
	this case, instead of using the foreach key as the name of the variable to look up, we have a second
	variable which is assigned a string value that includes the foreach key. This second variable is
	then used to determine the identifier.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternSeven(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternSeven(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternSeven(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-7 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case Expr e2 : {
							if ((e2@at)? && (e2@at == qr.l)) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,someExpr(var(name(name(v)))),_,_,_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("LP-7: Cannot use foreach, it creates an alias, <fe@at>");
							unres = unres + qr.l;
						} else {
							aexp = fe.arrayExpr;
							if (array(aelist) := aexp && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {
								if (hasDangerousUse(fe, v, fm)) {
									println("LP-7: Cannot use foreach, it has a potentially dangerous use");
									unres = unres + qr.l;
								} else if (addressTaken(c, v, fm)) {
									println("LP-7: Cannot use variable, its address is potentially taken, <v>");
									unres = unres + qr.l;
								} else {
									varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.key.expr | aeItem <- aelist }); 
									res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
								}
							} else {
								println("LP-7: Array expression <pp(aexp)> at <aexp@at> does not match pattern 7, <qr.l>");
								unres = unres + qr.l;
							}
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternSeven(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternSeven(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("seven"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Eight. Pattern eight is very similar to pattern four, but in
	this case, instead of using the foreach key as the name of the variable to look up, we have a second
	variable which is assigned a string value that includes the foreach key. This second variable is
	then used to determine the identifier.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternEight(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternEight(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternEight(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-8 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case Expr e2 : {
							if ((e2@at)? && (e2@at == qr.l)) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,some(var(name(name(v)))),_,_,_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("LP-8: Cannot use foreach, it creates an alias, <fe@at>");
							unres = unres + qr.l;
						} else {
							aexp = fe.arrayExpr;
							if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
								// TODO: Verify reachability
								//assignments = getStandardAssignmentsFor(aname, carrier(g));
								assignments = reachingDefs(c, aname, qr.e);
								if (size(assignments<1>) == 1) {
									assignLocs = assignments<0>;
									assignExpr = getOneFrom(assignments<1>);						
									if (array(aelist) := assignExpr.assignExpr && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {
										if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
											println("LP-8: Cannot use foreach, it has a potentially dangerous use");
											unres = unres + qr.l;
										} else if (addressTaken(c, v, fm)) {
											println("LP-8: Cannot use variable, its address is potentially taken, <v>");
											unres = unres + qr.l;
										} else {
											varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.key.expr | aeItem <- aelist }); 
											res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
										}
									} else {
										println("LP-8: Array expression <pp(aexp)> at <aexp@at> does not match pattern 8, <qr.l>");
										unres = unres + qr.l;
									}
								} else if (isEmpty(assignments<1>)) {
									println("LP-8: No local assignments, cannot use variable <aname>, <qr.l>");
									unres = unres + qr.l;
								} else {
									println("LP-8: Inconsistent assignments, cannot use variable <aname>, <qr.l>");
									unres = unres + qr.l;
								}							
							} else {
								println("LP-8: Array expression in foreach <pp(aexp)> does not match pattern 8, <qr.l>");
								unres = unres + qr.l;
							}
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternEight(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternEight(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("eight"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Nine. Pattern nine is very similar to pattern one, but in
	this case, instead of using the foreach value as the name of the variable to look up, we use this
	variable as part of an expression that yields a string, using this to find the identifier. This is
	different from pattern five because the expression is given inline, directly as the name of the
	identifier, and is not assigned into a second variable first.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternNine(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternNine(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats loopPatternNine(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);
	
	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-9 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getSingleVar(getVariablePart(e));
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-9: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (array(aelist) := aexp && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
							if (hasDangerousUse(fe, v, fm)) {
								println("LP-9: Cannot use foreach, it has a potentially dangerous use, <fe@at>");
								unres = unres + qr.l;
							} else if (addressTaken(c, v, fm)) {
								println("LP-9: Cannot use variable, its address is potentially taken, <v>");
								unres = unres + qr.l;
							} else {
								varExprs = replaceInExpr(getVariablePart(e), v, { aeItem.val | aeItem <- aelist }); 
								res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
							}
						} else {
							println("LP-9: Array expression <pp(aexp)> does not match pattern 9, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternNine(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternNine(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("nine"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Ten. Pattern ten is very similar to pattern two, but in
	this case, instead of using the foreach value as the name of the variable to look up, we use this
	variable as part of an expression that yields a string, using this to find the identifier. This is
	different from pattern six because the expression is given inline, directly as the name of the
	identifier, and is not assigned into a second variable first.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternTen(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternTen(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternTen(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-10 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getSingleVar(getVariablePart(e));
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-10: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
							// TODO: Verify reachability
							//assignments = getStandardAssignmentsFor(aname, carrier(g));
							assignments = reachingDefs(c, aname, qr.e);
							if (size(assignments<1>) == 1) {
								assignLocs = assignments<0>;
								assignExpr = getOneFrom(assignments<1>);						
								if (array(aelist) := assignExpr.assignExpr && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
									if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
										println("LP-10: Cannot use foreach, it has a potentially dangerous use");
										unres = unres + qr.l;
									} else if (addressTaken(c, v, fm)) {
										println("LP-10: Cannot use variable, its address is potentially taken, <v>");
										unres = unres + qr.l;
									} else {
										varExprs = replaceInExpr(getVariablePart(e), v, { aeItem.val | aeItem <- aelist });
										res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) }; 
									}
								} else {
									println("LP-10: Array expression <pp(aexp)> at <aexp@at> does not match pattern 10, <qr.l>");
									unres = unres + qr.l;
								}
							} else if (isEmpty(assignments<1>)) {
								println("LP-10: No local assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							} else {
								println("LP-10: Inconsistent assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							}							
						} else {
							println("LP-10: Array expression in foreach <pp(aexp)> does not match pattern 10, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternTen(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternTen(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("ten"),s));
	}
	
	return res;
}


@doc{
	Resolve variable definitions for Pattern Eleven. Pattern eleven is very similar to pattern three, 
	but in this case, instead of using the foreach key as the name of the variable to look up, we use
	this variable as part of an expression that yields a string, using this to find the identifier. 
	This is different from pattern seven because the expression is given inline, directly as the name 
	of the identifier, and is not assigned into a second variable first.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternEleven(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternEleven(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats loopPatternEleven(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);
	
	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-11 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
			
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getSingleVar(getVariablePart(e));
			
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,someExpr(var(name(name(v)))),_,_,_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-11: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (array(aelist) := aexp && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {
							if (hasDangerousUse(fe, v, fm)) {
								println("LP-11: Cannot use foreach, it has a potentially dangerous use, <fe@at>");
								unres = unres + qr.l;
							} else if (addressTaken(c, v, fm)) {
								println("LP-11: Cannot use variable, its address is potentially taken, <v>");
								unres = unres + qr.l;
							} else {
								varExprs = replaceInExpr(getVariablePart(e), v, { aeItem.key.expr | aeItem <- aelist }); 
								res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
							}
						} else {
							println("LP-11: Array expression <pp(aexp)> does not match pattern 11, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternEleven(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternEleven(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("eleven"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Twelve. Pattern twelve is very similar to pattern four, 
	but in this case, instead of using the foreach key as the name of the variable to look up, we use
	this variable as part of an expression that yields a string, using this to find the identifier. 
	This is different from pattern eight because the expression is given inline, directly as the name 
	of the identifier, and is not assigned into a second variable first.

	TODO: Add example
}
public rel[loc,AnalysisName] loopPatternTwelve(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternTwelve(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats loopPatternTwelve(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-12 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getSingleVar(getVariablePart(e));
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,someExpr(var(name(name(v)))),_,_,_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("LP-12: Cannot use foreach, it creates an alias, <fe@at>");
						unres = unres + qr.l;
					} else {
						aexp = fe.arrayExpr;
						if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
							// TODO: Verify reachability
							//assignments = getStandardAssignmentsFor(aname, carrier(g));
							assignments = reachingDefs(c, aname, qr.e);
							if (size(assignments<1>) == 1) {
								assignLocs = assignments<0>;
								assignExpr = getOneFrom(assignments<1>);			
								if (array(aelist) := assignExpr.assignExpr && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {			
									if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
										println("LP-12: Cannot use foreach, it has a potentially dangerous use");
									} else if (addressTaken(c, v, fm)) {
										println("LP-12: Cannot use variable, its address is potentially taken, <v>");
										unres = unres + qr.l;
									} else {
										varExprs = replaceInExpr(getVariablePart(e), v, { aeItem.key.expr | aeItem <- aelist }); 
										res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
									}
								} else {
									println("LP-12: Array expression <pp(aexp)> at <aexp@at> does not match pattern 12, <qr.l>");
									unres = unres + qr.l;
								}
							} else if (isEmpty(assignments<1>)) {
								println("LP-12: No local assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							} else {
								println("LP-12: Inconsistent assignments, cannot use variable <aname>, <qr.l>");
								unres = unres + qr.l;
							}							
						} else {
							println("LP-12: Array expression in foreach <pp(aexp)> does not match pattern 12, <qr.l>");
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternTwelve(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternTwelve(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("twelve"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern One. Pattern one is the following:
	
	1. A foreach loop is defined that works directly over a literal array
	2. Each element of this array is assigned into the foreach variable representing the value
	3. This foreach variable is used directly as the name of the variable being accessed

	TODO: Add example here
	
	We can resolve this under the restriction that the foreach variable is not used
	in a way where it could be modified (it is not passed to a function or method
	as a reference parameter, it is not reference assigned to another variable, it
	is not used as the target of an assignment). This also needs to occur in the
	context of the foreach that provides the variable.
}
public rel[loc,AnalysisName] loopPatternThirteen(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternThirteen(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats loopPatternThirteen(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);
	
	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-13 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);

				// We have a variable feature use, so get the actual variable used to hold it
				str v = getSingleVar(getVariablePart(e));
				
				// Find a surrounding for loop that initializes this
				Script s = pt[qr.l.top];
				list[Stmt] fors = [];
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							fors = [ fe | cn <- getTraversalContextNodes(), 
										  Stmt fe:\for([_*,assign(var(name(name(v))),scalar(integer(_))),_*],_,[_*,incop,_*],_) := cn,
							assign(var(name(name(v))),_) := incop || assignWOp(var(name(name(v))),_,_) := incop || unaryOperation(var(name(name(v))),_) := incop ];
						} 
					}
				}
				
				if (!isEmpty(fors)) {
					fe = fors[0];
					forRange = getForRange(fe,v);
					if (hasDangerousUse(fe, v, fm, ignoreLocs = { vassign@at | vassign:assign(var(name(name(v))),scalar(integer(_))) <- fe.inits, vassign@at? })) {
						println("LP-13: Cannot use for-initialized variable, it has a potentially dangerous use, <fe@at>");
						unres = unres + qr.l;
					} else if (addressTaken(c, v, fm)) {
						println("LP-13: Cannot use variable, its address is potentially taken, <v>");
						unres = unres + qr.l;
					} else {
						varExprs = replaceInExpr(getVariablePart(e), v, { scalar(string("<rnum>")) | rnum <- forRange });
						toAdd = { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
						if (size(toAdd) > 0) { 
							res = res + toAdd;
						} else {
							unres = unres + qr.l;
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternThirteen(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternThirteen(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("thirteen"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern One. Pattern one is the following:
	
	1. A foreach loop is defined that works directly over a literal array
	2. Each element of this array is assigned into the foreach variable representing the value
	3. This foreach variable is used directly as the name of the variable being accessed

	TODO: Add example here
	
	We can resolve this under the restriction that the foreach variable is not used
	in a way where it could be modified (it is not passed to a function or method
	as a reference parameter, it is not reference assigned to another variable, it
	is not used as the target of an assignment). This also needs to occur in the
	context of the foreach that provides the variable.
}
public rel[loc,AnalysisName] loopPatternFourteen(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return loopPatternFourteen(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats loopPatternFourteen(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("LP-14 WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);

				// We have a variable feature use, so get the actual variable used to hold it
				str av = getSingleVar(getVariablePart(e));
				
				// Get the assignments into this variable
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
				
					// Find a surrounding for loop that initializes this
					Script s = pt[qr.l.top];
					list[Stmt] fors = [];
					visit(s) {
						case Expr e2 : {
							if ((e2@at)? && (e2@at == qr.l)) {
								fors = [ fe | cn <- getTraversalContextNodes(), 
											  Stmt fe:\for([_*,assign(var(name(name(v))),scalar(integer(_))),_*],_,[_*,incop,_*],_) := cn,
								assign(var(name(name(v))),_) := incop || assignWOp(var(name(name(v))),_,_) := incop || unaryOperation(var(name(name(v))),_) := incop ];
							} 
						}
					}
					
					if (!isEmpty(fors)) {
						fe = fors[0];
						forRange = getForRange(fe,v);
						if (hasDangerousUse(fe, v, fm, ignoreLocs = { vassign@at | vassign:assign(var(name(name(v))),scalar(integer(_))) <- fe.inits, vassign@at? })) {
							println("LP-14: Cannot use for-initialized variable <av>, it has a potentially dangerous use, <fe@at>, < avAssign<0> >");
							unres = unres + qr.l;
						} else if (addressTaken(c, v, fm)) {
							println("LP-14: Cannot use variable, its address is potentially taken, <v>");
							unres = unres + qr.l;
						} else {
							varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { scalar(string("<rnum>")) | rnum <- forRange });
							toAdd = { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
							if (size(toAdd) > 0) {
								res = res + toAdd;
							} else {
								unres = unres + qr.l;
							}
						}
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] loopPatternFourteen(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = loopPatternFourteen(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("fourteen"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Twenty One. In this pattern, we have a variable that is
	used to hold the name of the identifier, and use assignments into this variable to determine the
	possible names. This pattern does not involve the use of a foreach loop, unlike earlier patterns.
}
public rel[loc,AnalysisName] flowPatternOne(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return flowPatternOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats flowPatternOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved) {
			if (/fulltext_native/ := qr.l.path) {
				println("Found it!");
			}
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				try {
					vp = getVariablePart(qr.e);
					if (propertyFetch(_,name(name(s))) := vp) {
						if (definiteUsablePropertyAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStringsWithChaining(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						} else if (potentialPropertyAssignment(c, s, qr.e)) {
							unres = unres + qr.l;
						}
					} else if (var(name(name(s))) := vp) {
						if (definiteUsableVariableAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStringsWithChaining(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						} else if (potentialVariableAssignment(c, s, qr.e)) {
							unres = unres + qr.l;
						}
					}
				} catch _ : {
					continue;
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] flowPatternOne(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = flowPatternOne(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("twentyone"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Twenty Two. This is similar to Pattern Twenty One, but focuses
	on a corner case, where the name comes from ternary conditionals that give different strings.
}
public rel[loc,AnalysisName] flowPatternTwo(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return flowPatternTwo(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats flowPatternTwo(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				try {
					vp = getVariablePart(qr.e);
					if (propertyFetch(_,name(name(s))) := vp) {
						if (definiteUsablePropertyAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStrings2(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						} else if (potentialPropertyAssignment(c, s, qr.e)) {
							unres = unres + qr.l;
						}
					} else if (var(name(name(s))) := vp) {
						if (definiteUsableVariableAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStrings2(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						} else if (potentialVariableAssignment(c, s, qr.e)) {
							unres = unres + qr.l;
						}
					}
				} catch _ : {
					continue;
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] flowPatternTwo(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = flowPatternTwo(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("twentytwo"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Twenty Three. This is similar to Pattern Twenty One, but focuses
	on a corner case, where the name comes from an array of strings that we are indexing into.
}
public rel[loc,AnalysisName] flowPatternThree(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return flowPatternThree(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats flowPatternThree(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			// TODO: CHECK ARRAY ASSIGNMENT TO ENSURE THIS PATTERN WORKS!
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				try {
					vp = getVariablePart(qr.e);
					if (fetchArrayDim(var(name(name(v))),_) := vp) {
						if (definiteUsableVariableAssignment(c, v, qr.e)) {
							assigned = gatherArrayOfStringsWithChaining(c, var(name(name(v))));
							res = res + { < qr.l, varName(as) > | as <- assigned };
						} else if (potentialVariableAssignment(c, v, qr.e)) {
							unres = unres + qr.l;
						}
					}
				} catch _ : {
					continue;
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] flowPatternThree(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = flowPatternThree(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("twentythree"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Twenty Three. This is similar to Pattern Twenty One, but handles
	the case where the variable or property name isn't used directly, but is instead used inside an expression
	that can be resolved to a string.
}
public rel[loc,AnalysisName] flowPatternFour(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return flowPatternFour(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats flowPatternFour(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, containsSingleVar(getVariablePart(qr.e))) {
			if (/fulltext_native/ := qr.l.path) {
				println("Found it!");
			}

			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				try {
					// We have a variable feature use, so get the actual variable used to hold it
					str v = getSingleVar(getVariablePart(qr.e));
					if (definiteUsableVariableAssignment(c, v, qr.e)) {
						assigned = gatherAssignedStringsWithChaining(c, var(name(name(v))));
						// TODO: Check for dangerous uses, excluding assignment locs
						varExprs = { replaceInExpr(getVariablePart(qr.e), v, scalar(string(asi))) | asi <- assigned };
						toAdd = { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
						if (size(toAdd) > 0) { 
							res = res + toAdd;
						} else {
							unres = unres + qr.l;
						}
					} else if (potentialVariableAssignment(c, v, qr.e)) {
						unres = unres + qr.l;
					}
				} catch _ : {
					continue;
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] flowPatternFour(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = flowPatternFour(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("twentyfour"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Twenty Three. This is similar to Pattern Twenty One, but handles
	the case where the variable or property name isn't used directly, but is instead used inside an expression
	that can be resolved to a string.
}
public rel[loc,AnalysisName] flowPatternFive(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return flowPatternFive(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats flowPatternFive(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	//scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved) {
			//CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			//if (emptyCFG() := c) {
			//	println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			//} else {
				try {
					vp = getVariablePart(qr.e);
					if (vp is ternary) {
						assigned = ternaryStringResults(algebraicSimplification(vp));
						if (size(assigned) > 0) {
							res = res + { < qr.l, varName(as) > | as <- assigned };
						} else {
							unres = unres + qr.l;
						}
					} 
				} catch _ : {
					continue;
				}
			//}
		}
		 
		return < res, unres >;
	}

	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] flowPatternFive(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = flowPatternFive(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("twentyfive"),s));
	}
	
	return res;
}

public bool containsSingleVar(Expr e, set[str] toIgnore = { }) {
	vars = { v | /v:var(_) := e, var(name(name(s))) !:= v || (var(name(name(s))) := v && s notin toIgnore) };
	if (size(vars) == 1 && var(name(name(_))) := getOneFrom(vars)) {
		return true;
	}
	return false;
}

public bool containsSingleVarOrProperty(Expr e, set[str] toIgnore = { }) {
	vars = { v | /v:var(_) := e, var(name(name(s))) !:= v || (var(name(name(s))) := v && s notin toIgnore) };
	if (size(vars) == 1 && var(name(name(_))) := getOneFrom(vars)) {
		return true;
	}
	return false;
}

public str getSingleVar(Expr e, set[str] toIgnore = { }) {
	vars = { s | /v:var(name(name(s))) := e && s notin toIgnore };
	return getOneFrom(vars);
}

public Expr replaceInExpr(Expr e, str v, Expr r) {
	return visit(e) {
		case var(name(name(v))) => r
	}
}

public set[Expr] replaceInExpr(Expr e, str v, set[Expr] rs) {
	return { replaceInExpr(e,v,r) | r <- rs };
}


private loc dataLoc = baseLoc + "serialized/vvInfo";

public void extractVVInfo(Corpus corpus) {
	if (!exists(dataLoc)) {
		mkDirectory(dataLoc);
	}
	
	for (s <- corpus) {
		pt = loadBinary(s,corpus[s]);
		vv = toVVInfo(getAllVV(s,corpus[s],pt));
		writeBinaryValueFile(dataLoc + "<s>-<corpus[s]>.vvinfo", vv, compression=false);
	}
}

public VVInfo loadVVInfo(Corpus corpus, str s) {
	return readBinaryValueFile(#VVInfo, dataLoc + "<s>-<corpus[s]>.vvinfo");
}

private loc resultLoc = baseLoc + "serialized/ase2015";

public void writePatternStats(str pname, map[str s, PatternStats p] stats) {
	if (!exists(resultLoc)) {
		mkDirectory(resultLoc);
	}
	writeBinaryValueFile(resultLoc + "pattern-<pname>.bin", stats, compression=false);
}

public map[str s, PatternStats p] readPatternStats(str pname) {
	return readBinaryValueFile(#map[str s, PatternStats p], resultLoc + "pattern-<pname>.bin");
}

public PatternStats readPatternStatsFor(str pname, str s) {
	return readPatternStats(pname)[s];
}

public set[loc] patternResolvedLocs(set[str] pnames, str s) {
	return { *patternResolvedLocs(pname,s) | pname <- pnames };
}

public set[loc] patternResolvedLocs(list[str] pnames, str s) {
	return { *patternResolvedLocs(pname,s) | pname <- pnames };
}

public set[loc] patternResolvedLocs(str pname, str s) {
	pstats = readPatternStatsFor(pname, s);
	return pstats.vvuses.resolvedLocs<0> + pstats.vvcalls.resolvedLocs<0> + pstats.vvmcalls.resolvedLocs<0> + pstats.vvnews.resolvedLocs<0> + pstats.vvprops.resolvedLocs<0> +
		pstats.vvcconsts.resolvedLocs<0> + pstats.vvscalls.resolvedLocs<0> + pstats.vvstargets.resolvedLocs<0> + pstats.vvsprops.resolvedLocs<0> + pstats.vvsptargets.resolvedLocs<0>;
		
}

private list[ParamInfo] plist2pilist(list[SummaryParam] plist) {
	return [ paramInfo( (pi has paramName) ? pi.paramName : "", /Ref/ := getName(pi) ) | pi <- plist ];
}

data FMParamInfo = fmParamInfo(rel[str fname, list[ParamInfo] parameterInfo] functions, rel[str fname, list[ParamInfo] parameterInfo] methods);

public FMParamInfo extractFunctionInfo(System s) {
	// First, get back all the library functions and methods so we can add
	// nodes in the call graph for those that are (or may be) used
	fsum = loadFunctionSummaries();
	msum = loadMethodSummaries();
	
	// Second, generate signatures for each of the scripts, so we know
	// what functions and methods are available
	// TODO: This does not handle varargs reference functions, should verify these don't occur in practice
	map[loc,Signature] sysSignatures = ( l : getFileSignature(l,s[l],buildInfo=true) | l <- s );

	rel[str fname, list[ParamInfo] parameterInfo] functions = 
		{ < fn, pi > | /functionSig([_*,function(fn)], list[ParamInfo] pi) := sysSignatures } +
		{ < fn, plist2pilist(plist) > | functionSummary([_*,function(fn)],plist,_,_,_,_) <- fsum };
	rel[str mname, list[ParamInfo] parameterInfo] methods = 
		{ < mn, pi > | /methodSig([_*,method(mn)], list[ParamInfo] pi) := sysSignatures } +
		{ < mn, plist2pilist(plist) > | methodSummary([_*,function(fn)],_,plist,_,_,_,_) <- msum };
		
	return fmParamInfo(functions, methods);
}

private loc functionInfoLoc = baseLoc + "serialized/functionInfo";

public void writeFunctionInfo(Corpus corpus, str s, FMParamInfo fp) {
	writeBinaryValueFile(functionInfoLoc + "<s>-<corpus[s]>.finfo", fp, compression=false);
}

public FMParamInfo readFunctionInfo(Corpus corpus, str s) {
	return readBinaryValueFile(#FMParamInfo, functionInfoLoc + "<s>-<corpus[s]>.finfo");
}

public void extractFunctionInfo(Corpus corpus) {
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		fp = extractFunctionInfo(pt);
		writeFunctionInfo(corpus, s, fp);
	}
}

public str patternResultsAsLatex(map[str s, PatternStats p] pstats, str pname, Corpus corpus) {
							 
	ci = loadCountsCSV();
	
	str headerLine() {
		return "System & \\multicolumn{17}{c}{Resolved Variable Features, Pattern <pname>} \\\\
		       '\\cmidrule{2-18}
		       ' & \\multicolumn{2}{c}{Variables} & \\phantom{a} & \\multicolumn{2}{c}{Function Calls} & \\phantom{a} & \\multicolumn{2}{c}{Method Calls} & \\phantom{a} & \\multicolumn{2}{c}{Property Fetches} & \\phantom{a} & \\multicolumn{2}{c}{Instantiations} & \\phantom{a} & \\multicolumn{2}{c}{All} \\\\
		       '\\cmidrule{2-3} \\cmidrule{5-6} \\cmidrule{8-9} \\cmidrule{11-12} \\cmidrule{14-15} \\cmidrule{17-18}
		       ' & Resolved & Unresolved && Resolved & Unresolved && Resolved & Unresolved && Resolved & Unresolved && Resolved & Unresolved && Resolved & Unresolved \\\\ \\midrule";
	}
	
	str c(ResolveStats vv) = "\\numprint{<vv.resolved>} & \\numprint{<size(vv.unresolvedLocs)>}";
	
	int allResolved(str p) = pstats[p].vvuses.resolved + pstats[p].vvcalls.resolved + pstats[p].vvmcalls.resolved + pstats[p].vvnews.resolved + pstats[p].vvprops.resolved +
		pstats[p].vvcconsts.resolved + pstats[p].vvscalls.resolved + pstats[p].vvstargets.resolved + pstats[p].vvsprops.resolved + pstats[p].vvsptargets.resolved;

	int allUnresolved(str p) = size(pstats[p].vvuses.unresolvedLocs + pstats[p].vvcalls.unresolvedLocs + pstats[p].vvmcalls.unresolvedLocs + pstats[p].vvnews.unresolvedLocs + pstats[p].vvprops.unresolvedLocs +
		pstats[p].vvcconsts.unresolvedLocs + pstats[p].vvscalls.unresolvedLocs + pstats[p].vvstargets.unresolvedLocs + pstats[p].vvsprops.unresolvedLocs + pstats[p].vvsptargets.unresolvedLocs);

	int allUses(VVInfo vvi) = size(vvi.vvuses) + size(vvi.vvcalls) + size(vvi.vvmcalls) + size(vvi.vvnews) + size(vvi.vvprops) +
		size(vvi.vvcconsts) + size(vvi.vvscalls) + size(vvi.vvstargets) + size(vvi.vvsprops) + size(vvi.vvsptargets);
		
	str productLine(str p) {
		< lineCount, fileCount > = getOneFrom(ci[p,corpus[p]]);
		vvi = loadVVInfo(corpus,p);
		return "<p> & <c(pstats[p].vvuses)> && <c(pstats[p].vvcalls)> && <c(pstats[p].vvmcalls)> && <c(pstats[p].vvprops)> && <c(pstats[p].vvnews)> && \\numprint{<allResolved(p)>} & \\numprint{<allUnresolved(p)>} \\\\";
	}

	res = "\\npaddmissingzero
		  '\\npfourdigitsep
		  '\\begin{table*}
		  '\\centering
		  '\\caption{PHP Variable Features Resolved By Pattern <pname>.\\label{table-var-pattern-<pname>}}
		  '\\ra{1.0}
		  '\\resizebox{\\textwidth}{!}{%
		  '\\begin{tabular}{@{}lrrcrrcrrcrrcrrcrr@{}} \\toprule 
		  '<headerLine()> <for (p <- sort(toList(corpus<0>),bool(str s1,str s2) { return toUpperCase(s1)<toUpperCase(s2); })) {>
		  '  <productLine(p)> <}>
		  '\\bottomrule
		  '\\end{tabular}
		  '}
		  '\\end{table*}
		  '";
	return res;
}

public str patternResultsAsLatexForAll(map[str s, PatternStats p] pstats, str pname, Corpus corpus) {
							 
	ci = loadCountsCSV();
	
	str headerLine() {
		return "System & \\multicolumn{17}{c}{Resolved Variable Features, Pattern <pname>} \\\\
		       '\\cmidrule{2-18}
		       ' & \\multicolumn{2}{c}{Variables} & \\phantom{a} & \\multicolumn{2}{c}{Function Calls} & \\phantom{a} & \\multicolumn{2}{c}{Method Calls} & \\phantom{a} & \\multicolumn{2}{c}{Property Fetches} & \\phantom{a} & \\multicolumn{2}{c}{Instantiations} & \\phantom{a} & \\multicolumn{2}{c}{All} \\\\
		       '\\cmidrule{2-3} \\cmidrule{5-6} \\cmidrule{8-9} \\cmidrule{11-12} \\cmidrule{14-15} \\cmidrule{17-18}
		       ' & Resolved & Uses && Resolved & Uses && Resolved & Uses && Resolved & Uses && Resolved & Uses && Resolved & Uses \\\\ \\midrule";
	}
	
	str c(ResolveStats vv, int n) = "\\numprint{<vv.resolved>} & \\numprint{<n>}";
	
	int allResolved(str p) = pstats[p].vvuses.resolved + pstats[p].vvcalls.resolved + pstats[p].vvmcalls.resolved + pstats[p].vvnews.resolved + pstats[p].vvprops.resolved +
		pstats[p].vvcconsts.resolved + pstats[p].vvscalls.resolved + pstats[p].vvstargets.resolved + pstats[p].vvsprops.resolved + pstats[p].vvsptargets.resolved;

	int allUses(VVInfo vvi) = size(vvi.vvuses) + size(vvi.vvcalls) + size(vvi.vvmcalls) + size(vvi.vvnews) + size(vvi.vvprops) +
		size(vvi.vvcconsts) + size(vvi.vvscalls) + size(vvi.vvstargets) + size(vvi.vvsprops) + size(vvi.vvsptargets);
		
	str productLine(str p) {
		< lineCount, fileCount > = getOneFrom(ci[p,corpus[p]]);
		vvi = loadVVInfo(corpus,p);
		vvusesCount = size(vvi.vvuses);
		vvcallsCount = size(vvi.vvcalls);
		vvmcallsCount = size(vvi.vvmcalls);
		vvpropsCount = size(vvi.vvprops);
		vvnewsCount = size(vvi.vvnews);
		return "<p> & <c(pstats[p].vvuses,vvusesCount)> && <c(pstats[p].vvcalls,vvcallsCount)> && <c(pstats[p].vvmcalls,vvmcallsCount)> && <c(pstats[p].vvprops,vvpropsCount)> && <c(pstats[p].vvnews,vvnewsCount)> && \\numprint{<allResolved(p)>} & \\numprint{<allUses(vvi)>} \\\\";
	}

	res = "\\npaddmissingzero
		  '\\npfourdigitsep
		  '\\begin{table*}
		  '\\centering
		  '\\caption{PHP Variable Features Resolved By Pattern <pname>.\\label{table-var-pattern-<pname>}}
		  '\\ra{1.0}
		  '\\resizebox{\\textwidth}{!}{%
		  '\\begin{tabular}{@{}lrrcrrcrrcrrcrrcrr@{}} \\toprule 
		  '<headerLine()> <for (p <- sort(toList(corpus<0>),bool(str s1,str s2) { return toUpperCase(s1)<toUpperCase(s2); })) {>
		  '  <productLine(p)> <}>
		  '\\bottomrule
		  '\\end{tabular}
		  '}
		  '\\end{table*}
		  '";
	return res;
}

private loc cfgLoc = baseLoc + "serialized/vvCFGs";

data CFGInfo = cfgInfo(loc forTopLevel, map[loc,loc] forContainers) | cfgInfoOnlyContainers(map[loc,loc] forContainers);

public void extractCFGs(Corpus corpus) {
	int uniqueIds = 1;
	for (s <- corpus) {
		map[loc,CFGInfo] infoMap = ( );
		pt = loadBinary(s, corpus[s]);
		vv = loadVVInfo(getBaseCorpus(), s);		
		vvAll = collapseVVInfo(vv);
		scriptLocs = { qr.l.top | qr <- vvAll };
		for (l <- scriptLocs) {
			scriptCFGs = buildCFGs(pt[l], buildBasicBlocks=false);
			ci = cfgInfoOnlyContainers(( ));
			if ([global()] in scriptCFGs) {
				ci = cfgInfo(cfgLoc + "cfg-<uniqueIds>.bin",( ));
				uniqueIds = uniqueIds + 1;
			}
			for (np <- scriptCFGs) {
				if ([global()] == np) {
					writeBinaryValueFile(ci.forTopLevel, scriptCFGs[np], compression=false);
				} else {
					toWrite = cfgLoc + "cfg-<uniqueIds>.bin";				
					uniqueIds = uniqueIds + 1;
					writeBinaryValueFile(toWrite, scriptCFGs[np], compression=false);
					ci.forContainers[scriptCFGs[np].at] = toWrite;
				}
			}
			infoMap[l] = ci; 
		}
		writeBinaryValueFile(cfgLoc+"<s>-<corpus[s]>.cfgmap", infoMap, compression=false);
	}
}

public map[loc,CFGInfo] loadCFGMap(Corpus corpus, str s) {
	return readBinaryValueFile(#map[loc,CFGInfo], cfgLoc+"<s>-<corpus[s]>.cfgmap");
}

public CFG loadCFG(loc l) {
	return readBinaryValueFile(#CFG, l);
}

public loc findMapEntry(CFGInfo ci, loc toFind) {
	for (l <- ci.forContainers) {
		if (l.offset <= toFind.offset && toFind.offset <= (l.offset + l.length)) {
			return ci.forContainers[l];
		}
	}
	if (ci has forTopLevel) {
		return ci.forTopLevel;
	}
	throw "No location to return for location to find <toFind>!";
}

public map[str s, PatternStats p] totalPatterns() {
	pstats = readPatternStats("one");
	pstats = addPatternStats(pstats, readPatternStats("two"));
	pstats = addPatternStats(pstats, readPatternStats("three"));
	pstats = addPatternStats(pstats, readPatternStats("four"));
	return pstats;
}

public bool definiteUsableVariableAssignment(CFG g, str v, Expr usedBy) {
	set[CFGNode] checked = { };
	ggraph = cfgAsGraph(g);
	
	bool assignedOnPath(CFGNode n) {
		// If we reach an exit node it doesn't matter, that means we have a path
		// where we don't have a definition but we also don't have a use.
		if (isExitNode(n)) {
			return true;
		}

		// If we find a use of the expression this means we have the use before the def
		if (exprNode(e,_) := n && e == usedBy && e@at == usedBy@at) {
			return false;
		}

		if (exprNode(assign(var(name(name(v))),aexp),_) := n, exprIsScalarStringOrChained(aexp)) {
			return true;
		}
		toCheck = { gi | gi <- ggraph[n], gi notin checked };
		checked = checked + toCheck;
		results = { assignedOnPath(gi) | gi <- toCheck };
		return false notin results;
	}
		
	try {
		return assignedOnPath(getEntryNode(g));
	} catch xval : {
		return false;
	}
}

public bool definiteVariableAssignment(CFG g, str v, Expr usedBy) {
	set[CFGNode] checked = { };
	ggraph = cfgAsGraph(g);
	
	bool assignedOnPath(CFGNode n) {
		// If we reach an exit node it doesn't matter, that means we have a path
		// where we don't have a definition but we also don't have a use.
		if (isExitNode(n)) {
			return true;
		}

		// If we find a use of the expression this means we have the use before the def
		if (exprNode(e,_) := n && e == usedBy && e@at == usedBy@at) {
			return false;
		}

		if (exprNode(assign(var(name(name(v))),aexp),_) := n) {
			return true;
		}
		toCheck = { gi | gi <- ggraph[n], gi notin checked };
		checked = checked + toCheck;
		results = { assignedOnPath(gi) | gi <- toCheck };
		return false notin results;
	}
		
	try {
		return assignedOnPath(getEntryNode(g));
	} catch xval : {
		return false;
	}
}

public rel[loc,Expr] reachingDefs(CFG g, str v, Expr usedBy) {
	rel[loc,Expr] assignments = { };
	set[CFGNode] checked = { };

	if (!definiteVariableAssignment(g, v, usedBy)) return assignments;

	ggraph = invert(cfgAsGraph(g));
	startingNodes = { gn | gn:exprNode(en,_) <- g.nodes, en@at?, usedBy@at?, en@at == usedBy@at };
	if (size(startingNodes) != 1) {
		println("WARNING: Wrong number of starting nodes for <usedBy> at location <usedBy@at>, found <size(startingNodes)>");
		return assignments;
	}
	startingNode = getOneFrom(startingNodes);
	
	void getDefs(CFGNode n) {
		// TODO: Account for other styles of assignment into the variable
		if (exprNode(ae:assign(var(name(name(v))),aexp),_) := n) {
			assignments = assignments + < ae@at, ae >;
		} else {
			toCheck = { gi | gi <- ggraph[n], gi notin checked };
			checked = checked + toCheck;
			for (gi <- toCheck) {
				getDefs(gi);
			}
		}
	}
		
	getDefs(startingNode);
	return assignments;
}

public bool definiteUsablePropertyAssignment(CFG g, str v, Expr usedBy) {
	set[CFGNode] checked = { };
	ggraph = cfgAsGraph(g);
	
	bool assignedOnPath(CFGNode n) {
		// If we reach an exit node it doesn't matter, that means we have a path
		// where we don't have a definition but we also don't have a use.
		if (isExitNode(n)) return true;

		// If we find a use of the expression this means we have the use before the def
		if (exprNode(e,_) := n && e == usedBy && e@at == usedBy@at) {
			return false;
		}

		if (exprNode(assign(propertyFetch(_,name(name(v))),aexp),_) := n, exprIsScalarStringOrChained(aexp)) return true;
		toCheck = { gi | gi <- ggraph[n], gi notin checked };
		checked = checked + toCheck;
		results = { assignedOnPath(gi) | gi <- toCheck };
		return false notin results;
	}
		
	try {
		return assignedOnPath(getEntryNode(g));
	} catch xval : {
		return false;
	}
}


public bool potentialVariableAssignment(CFG g, str v, Expr usedBy) {
	return (/exprNode(assign(var(name(name(v))),_),_) := carrier(cfgAsGraph(g)));
}

public bool potentialPropertyAssignment(CFG g, str v, Expr usedBy) {
	return (/exprNode(assign(propertyFetch(_,name(name(v))),_),_) := carrier(cfgAsGraph(g)));
}

public set[str] basicReachingDefs(CFG g, str v, Expr usedBy) {
	ggraph = cfgAsGraph(g);

	// First, what are the possible assignments to v?
	allDefs = { };
	rel[Lab,str] startingDefs = { };
	
	for (exprNode(assign(var(name(name(v))), Expr toAssign), l) <- g) {
		if (exprIsScalarStringOrChained(toAssign)) {
			s = getScalarStringOrChained(toAssign);
			startingDefs = startingDefs + < l, s >;
			allDefs = allDefs + s;
		} else {
			return { }; // We cannot use this if we have assignments that we cannot resolve
		}
	}
		
	
	set[CFGNode] checked = { };
	
	set[str] assignedOnPath(CFGNode n, set[str] foundSoFar) {
		// If we trigger this, this means we have reached the end of the function without
		// actually encountering the expression that uses variable v. If that is the case,
		// we just return the empty set since we don't want this to impact the rest of the
		// analysis.
		if (isExitNode(n)) {
			return { };
		}

		// If this matches, we have found the using expression along this path. Return the
		// set of reachable names.
		if (exprNode(e,_) := n && e == usedBy && e@at == usedBy@at) {
			return foundSoFar;
		}

		// If this matches, 
		if (exprNode(assign(var(name(name(v))),Expr toAssign),_) := n) {
			if (exprIsScalarStringOrChained(toAssign)) {
				foundSoFar = foundSoFar + getScalarStringOrChained(toAssign); 
			} else {
				throw "We cannot use this variable, we have unresolvable assignments";
			}
		}
		toCheck = { gi | gi <- ggraph[n], gi notin checked };
		checked = checked + toCheck;
		results = { *assignedOnPath(gi, foundSoFar) | gi <- toCheck };
		return results;
	}
		
	try {
		return assignedOnPath(getEntryNode(g));
	} catch xval : {
		return false;
	}
}

public void runExtracts() {
	corpus = getBaseCorpus();
	extractVVInfo(corpus);
	extractFunctionInfo(corpus);	
	extractCFGs(corpus);	
}

public void runPatterns() {
	corpus = getBaseCorpus();

//	println("Running Pattern One");
//	writePatternStats("one", loopPatternOne(corpus));
//
//	println("Running Pattern Two");
//	writePatternStats("two", loopPatternTwo(corpus));
//
//	println("Running Pattern Three");
//	writePatternStats("three", loopPatternThree(corpus));
//
//	println("Running Pattern Four");
//	writePatternStats("four", loopPatternFour(corpus));
//
//	println("Running Pattern Five");
//	writePatternStats("five", loopPatternFive(corpus));
//
//	println("Running Pattern Six");
//	writePatternStats("six", loopPatternSix(corpus));
//
//	println("Running Pattern Seven");
//	writePatternStats("seven", loopPatternSeven(corpus));
//
//	println("Running Pattern Eight");
//	writePatternStats("eight", loopPatternEight(corpus));
//
//	println("Running Pattern Nine");
//	writePatternStats("nine", loopPatternNine(corpus));
//
//	println("Running Pattern Ten");
//	writePatternStats("ten", loopPatternTen(corpus));
//
//	println("Running Pattern Eleven");
//	writePatternStats("eleven", loopPatternEleven(corpus));
//
//	println("Running Pattern Twelve");
//	writePatternStats("twelve", loopPatternTwelve(corpus));
//
//	println("Running Pattern Thirteen");
//	writePatternStats("thirteen", loopPatternThirteen(corpus));
//
//	println("Running Pattern Fourteen");
//	writePatternStats("fourteen", loopPatternFourteen(corpus));

	println("Running Pattern Twenty One");
	writePatternStats("twentyone", flowPatternOne(corpus));

	println("Running Pattern Twenty Two");
	writePatternStats("twentytwo", flowPatternTwo(corpus));

	println("Running Pattern Twenty Three");
	writePatternStats("twentythree", flowPatternThree(corpus));

	println("Running Pattern Twenty Four");
	writePatternStats("twentyfour", flowPatternFour(corpus));

	println("Running Pattern Twenty Five");
	writePatternStats("twentyfive", flowPatternFive(corpus));

	println("Running Pattern Thirty One");
	writePatternStats("thirtyone", assignmentPatternOne(corpus));

	println("Running Pattern Thirty Two");
	writePatternStats("thirtytwo", assignmentPatternTwo(corpus));

	println("Running Pattern Thirty Three");
	writePatternStats("thirtythree", assignmentPatternThree(corpus));

	println("Running Pattern Thirty Four");
	writePatternStats("thirtyfour", assignmentPatternFour(corpus));
}

public void runAntiPatterns() {
	corpus = getBaseCorpus();

	println("Running Anti-Pattern One");
	writePatternStats("antione", antiPatternOne(corpus));

	println("Running Anti-Pattern Two");
	writePatternStats("antitwo", antiPatternTwo(corpus));

	println("Running Anti-Pattern Three");
	writePatternStats("antithree", antiPatternThree(corpus));
}
	
public void generateLatex() {
	corpus = getBaseCorpus();
	paperLoc = |home:///Dropbox/Papers/2015/var-feature-resolution/|;
	
	writeFile(paperLoc+"vv-pattern-one.tex", patternResultsAsLatex(readPatternStats("one"), "one", corpus));	
	writeFile(paperLoc+"vv-pattern-two.tex", patternResultsAsLatex(readPatternStats("two"), "two", corpus));	
	writeFile(paperLoc+"vv-pattern-three.tex", patternResultsAsLatex(readPatternStats("three"), "three", corpus));	
	writeFile(paperLoc+"vv-pattern-four.tex", patternResultsAsLatex(readPatternStats("four"), "four", corpus));	
	writeFile(paperLoc+"vv-pattern-five.tex", patternResultsAsLatex(readPatternStats("five"), "five", corpus));	
	writeFile(paperLoc+"vv-pattern-six.tex", patternResultsAsLatex(readPatternStats("six"), "six", corpus));	
	writeFile(paperLoc+"vv-pattern-seven.tex", patternResultsAsLatex(readPatternStats("seven"), "seven", corpus));	
	writeFile(paperLoc+"vv-pattern-eight.tex", patternResultsAsLatex(readPatternStats("eight"), "eight", corpus));	
	writeFile(paperLoc+"vv-pattern-nine.tex", patternResultsAsLatex(readPatternStats("nine"), "nine", corpus));	
	writeFile(paperLoc+"vv-pattern-ten.tex", patternResultsAsLatex(readPatternStats("ten"), "ten", corpus));	
	writeFile(paperLoc+"vv-pattern-eleven.tex", patternResultsAsLatex(readPatternStats("eleven"), "eleven", corpus));	
	writeFile(paperLoc+"vv-pattern-twelve.tex", patternResultsAsLatex(readPatternStats("twelve"), "twelve", corpus));	
	writeFile(paperLoc+"vv-pattern-thirteen.tex", patternResultsAsLatex(readPatternStats("thirteen"), "thirteen", corpus));	
	writeFile(paperLoc+"vv-pattern-fourteen.tex", patternResultsAsLatex(readPatternStats("fourteen"), "fourteen", corpus));	

	writeFile(paperLoc+"vv-pattern-twenty-one.tex", patternResultsAsLatex(readPatternStats("twentyone"), "twentyone", corpus));	
	writeFile(paperLoc+"vv-pattern-twenty-two.tex", patternResultsAsLatex(readPatternStats("twentytwo"), "twentytwo", corpus));
	writeFile(paperLoc+"vv-pattern-twenty-three.tex", patternResultsAsLatex(readPatternStats("twentythree"), "twentythree", corpus));
	writeFile(paperLoc+"vv-pattern-twenty-four.tex", patternResultsAsLatex(readPatternStats("twentyfour"), "twentyfour", corpus));
	writeFile(paperLoc+"vv-pattern-twenty-five.tex", patternResultsAsLatex(readPatternStats("twentyfive"), "twentyfive", corpus));
	
	writeFile(paperLoc+"vv-pattern-thirty-one.tex", patternResultsAsLatex(readPatternStats("thirtyone"), "thirtyone", corpus));
	writeFile(paperLoc+"vv-pattern-thirty-two.tex", patternResultsAsLatex(readPatternStats("thirtytwo"), "thirtytwo", corpus));
	writeFile(paperLoc+"vv-pattern-thirty-three.tex", patternResultsAsLatex(readPatternStats("thirtythree"), "thirtythree", corpus));
	writeFile(paperLoc+"vv-pattern-thirty-four.tex", patternResultsAsLatex(readPatternStats("thirtyfour"), "thirtyfour", corpus));

//	pstats = readPatternStats("one");
//	pstats = addPatternStats(pstats,readPatternStats("two"));	
//	pstats = addPatternStats(pstats,readPatternStats("three"));	
//	pstats = addPatternStats(pstats,readPatternStats("four"));	
//	pstats = addPatternStats(pstats,readPatternStats("five"));	
//	pstats = addPatternStats(pstats,readPatternStats("six"));	
//	pstats = addPatternStats(pstats,readPatternStats("seven"));	
//	pstats = addPatternStats(pstats,readPatternStats("eight"));	
//	pstats = addPatternStats(pstats,readPatternStats("nine"));	
//	pstats = addPatternStats(pstats,readPatternStats("ten"));	
//	pstats = addPatternStats(pstats,readPatternStats("eleven"));	
//	pstats = addPatternStats(pstats,readPatternStats("twelve"));	
//	pstats = addPatternStats(pstats,readPatternStats("thirteen"));	
//	pstats = addPatternStats(pstats,readPatternStats("fourteen"));	
//
//	pstatsLoops = pstats;
//	writeFile(paperLoc+"vv-pattern-loops.tex", patternResultsAsLatex(pstatsLoops,"loops",corpus));
//	
//	pstats = readPatternStats("twentyone");	
//	pstats = addPatternStats(pstats,readPatternStats("twentytwo"));	
//	pstats = addPatternStats(pstats,readPatternStats("twentythree"));	
//	pstats = addPatternStats(pstats,readPatternStats("twentyfour"));	
//	pstats = addPatternStats(pstats,readPatternStats("twentyfive"));	
//
//	pstatsAssignments = pstats;
//	writeFile(paperLoc+"vv-pattern-assignments.tex", patternResultsAsLatex(pstatsAssignments,"assignments",corpus));
//	
//	pstats = readPatternStats("thirtyone");	
//	pstats = addPatternStats(pstats,readPatternStats("thirtytwo"));	
//	pstats = addPatternStats(pstats,readPatternStats("thirtythree"));	
//	pstats = addPatternStats(pstats,readPatternStats("thirtyfour"));	
//
//	pstatsFlow = pstats;
//	writeFile(paperLoc+"vv-pattern-flow.tex", patternResultsAsLatex(pstatsFlow,"flow",corpus));
//	
//	pstatsAll = addPatternStats(pstatsFlow, addPatternStats(pstatsAssignments, pstatsLoops));
//	writeFile(paperLoc+"vv-pattern-all.tex", patternResultsAsLatex(pstatsAll,"all",corpus));
}

public bool isUsefulCondExpression(Expr e, str v) {
	if (binaryOperation(var(name(name(v))),scalar(string(s)),equal()) := e ||
	    binaryOperation(var(name(name(v))),scalar(string(s)),identical()) := e ||
	    binaryOperation(scalar(string(s)),var(name(name(v))),equal()) := e ||
	    binaryOperation(scalar(string(s)),var(name(name(v))),identical()) := e) {
	    return true;
	} else if (binaryOperation(e1,e2,booleanOr()) := e) {
		return isUsefulCondExpression(e1,v) && isUsefulCondExpression(e2,v);
	}  else if (binaryOperation(e1,e2,logicalOr()) := e) {
		return isUsefulCondExpression(e1,v) && isUsefulCondExpression(e2,v);
	}
	
	return false;
	    
}

public bool maybeUsefulCondExpression(Expr e, str v) {
	return (/var(name(name(v))) := e);
}

public set[str] getUsefulCondExpressionValues(Expr e, str v) {
	if (binaryOperation(var(name(name(v))),scalar(string(s)),equal()) := e ||
	    binaryOperation(var(name(name(v))),scalar(string(s)),identical()) := e ||
	    binaryOperation(scalar(string(s)),var(name(name(v))),equal()) := e ||
	    binaryOperation(scalar(string(s)),var(name(name(v))),identical()) := e) {
	    return { s };
	} else if (binaryOperation(e1,e2,booleanOr()) := e) {
		return getUsefulCondExpressionValues(e1,v) + getUsefulCondExpressionValues(e2,v);
	}  else if (binaryOperation(e1,e2,logicalOr()) := e) {
		return getUsefulCondExpressionValues(e1,v) + getUsefulCondExpressionValues(e2,v);
	}
	
	return { };
	    
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] assignmentPatternOne(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return assignmentPatternOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats assignmentPatternOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			//println("Processing expression <pp(e)> at location <qr.l>");
			//CFG c = cfgForExpression(scriptCFGs[qr.l.top],e);
			//g = cfgAsGraph(c);
			if (/ucp_pm_compose/ := qr.l.path) {
				println("Found it!");
			}
			// We have a variable feature use, so get the actual variable used to hold it
			str v = getVariableName(e);
			
			// Find the node inside the system using a visit, that way we can also
			// find the containing foreach
			Script s = pt[qr.l.top];
			list[node] conditionalParts = [ ];
			visit(s) {
				case Expr e2 : {
					if ((e2@at)? && (e2@at == qr.l)) {
						conditionalParts = [ ce | ce <- getTraversalContextNodes(), (ce is \if || ce is \elseIf) ];
					} 
				}
			}
			
			if (!isEmpty(conditionalParts)) {
				part = conditionalParts[0]; conditionalParts = conditionalParts[1..];
				
				if (\if(Expr cond, list[Stmt] body, list[ElseIf] elseIfs, OptionElse elseClause) := part) {
					// If we are here, this means that the use is inside the body. See if the condition
					// is helpful.
					if (isUsefulCondExpression(cond,v)) {
						// TODO: See if we need this, not sure why I commented this out...
						//if (true in { hasDangerousUse(ci,v,fm) | ci <- body }) {
						//	// This means the conditional this was found in also has dangerous uses of the name,
						//	// so we should give up
						//	println("Dangerous uses of <v> found in conditional, no match at <qr.l>");
						//	return res;
						//}
						res = res + { < qr.l, varName(vi) > | vi <- getUsefulCondExpressionValues(cond, v) };
					} else if (maybeUsefulCondExpression(cond,v)) {
						unres = unres + qr.l;
					} else {
						println("Conditional expression <pp(cond)> is not useful, no match at <qr.l>");
					}
				} else if (elseIf(Expr cond, list[Stmt] body) := part) {
					// If we are here, this means the use is inside the elseIf body. See if the condition
					// is helpful
					if (isUsefulCondExpression(cond,v)) {
						// TODO: See if we need this, not sure why I commented this out...
						//if (true in { hasDangerousUse(ci,v,fm) | ci <- body }) {
						//	// This means the conditional this was found in also has dangerous uses of the name,
						//	// so we should give up
						//	println("Dangerous uses of <v> found in conditional, no match at <qr.l>");
						//	return res;
						//}
						res = res + { < qr.l, varName(vi) > | vi <- getUsefulCondExpressionValues(cond, v) };
					} else if (maybeUsefulCondExpression(cond,v)) {
						unres = unres + qr.l;
					} else {
						println("Conditional expression <pp(cond)> is not useful, no match at <qr.l>");
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] assignmentPatternOne(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = assignmentPatternOne(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("thirtyone"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] assignmentPatternTwo(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return assignmentPatternTwo(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats assignmentPatternTwo(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getVariableName(e);
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Case] cases = [ ];
				list[Stmt] switches = [ ];
				
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							fullPath = getTraversalContextNodes();
							caseFound = false;
							for (i <- index(fullPath)) {
								if (!caseFound && Case cf:\case(_,_) := fullPath[i]) {
									cases = cases + cf;
									caseFound = true;
								} else if (caseFound && Stmt sf:\switch(_,_) := fullPath[i]) {
									switches = switches + sf;
									break;
								}
							}
						} 
					}
				}
				
				if (!isEmpty(cases) && !isEmpty(switches)) {
					containingCase = cases[0];
					containingSwitch = switches[0];
					
					// Is this switch useful?
					if (var(name(name(v))) := containingSwitch.cond) {
						possibleCases = reachableCases(c, qr.e, containingSwitch.cases);
						caseValues = { sval | \case(someExpr(scalar(string(sval))),_) <- possibleCases };
						res = res + { < qr.l, varName(cv) > | cv <- caseValues };
					} else if (/var(name(name(v))) := containingSwitch.cond) {
						unres = unres + qr.l;
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] assignmentPatternTwo(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = assignmentPatternTwo(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("thirtytwo"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] assignmentPatternThree(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return assignmentPatternThree(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats assignmentPatternThree(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			//println("Processing expression <pp(e)> at location <qr.l>");
			//CFG c = cfgForExpression(scriptCFGs[qr.l.top],e);
			//g = cfgAsGraph(c);

			// We have a variable feature use, so get the actual variable used to hold it
			str v = getSingleVar(getVariablePart(e));
			
			// Find the node inside the system using a visit, that way we can also
			// find the containing foreach
			Script s = pt[qr.l.top];
			list[node] conditionalParts = [ ];
			visit(s) {
				case Expr e2 : {
					if ((e2@at)? && (e2@at == qr.l)) {
						conditionalParts = [ ce | ce <- getTraversalContextNodes(), (ce is \if || ce is \elseIf) ];
					} 
				}
			}
			
			if (!isEmpty(conditionalParts)) {
				part = conditionalParts[0]; conditionalParts = conditionalParts[1..];
				
				if (\if(Expr cond, list[Stmt] body, list[ElseIf] elseIfs, OptionElse elseClause) := part) {
					// If we are here, this means that the use is inside the body. See if the condition
					// is helpful.
					if (isUsefulCondExpression(cond,v)) {
						// TODO: See if we need this, not sure why I commented this out...
						//if (true in { hasDangerousUse(ci,v,fm) | ci <- body }) {
						//	// This means the conditional this was found in also has dangerous uses of the name,
						//	// so we should give up
						//	println("Dangerous uses of <v> found in conditional, no match at <qr.l>");
						//	return res;
						//}
						varExprs = replaceInExpr(getVariablePart(e), v, { scalar(string(sv)) | sv <- getUsefulCondExpressionValues(cond,v)});
						res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) }; 
					} else if (maybeUsefulCondExpression(cond,v)) {
						unres = unres + qr.l;
					} else {
						println("Conditional expression <pp(cond)> is not useful, no match at <qr.l>");
					}
				} else if (elseIf(Expr cond, list[Stmt] body) := part) {
					// If we are here, this means the use is inside the elseIf body. See if the condition
					// is helpful
					if (isUsefulCondExpression(cond,v)) {
						// TODO: See if we need this, not sure why I commented this out...
						//if (true in { hasDangerousUse(ci,v,fm) | ci <- body }) {
						//	// This means the conditional this was found in also has dangerous uses of the name,
						//	// so we should give up
						//	println("Dangerous uses of <v> found in conditional, no match at <qr.l>");
						//	return res;
						//}
						varExprs = replaceInExpr(getVariablePart(e), v, { scalar(string(sv)) | sv <- getUsefulCondExpressionValues(cond,v)});
						res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) }; 
					} else if (maybeUsefulCondExpression(cond,v)) {
						unres = unres + qr.l;
					} else {
						println("Conditional expression <pp(cond)> is not useful, no match at <qr.l>");
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] assignmentPatternThree(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = assignmentPatternThree(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("thirtythree"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] assignmentPatternFour(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return assignmentPatternFour(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats assignmentPatternFour(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, containsSingleVar(getVariablePart(e))) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getSingleVar(getVariablePart(e));
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Case] cases = [ ];
				list[Stmt] switches = [ ];
				
				visit(s) {
					case Expr e2 : {
						if ((e2@at)? && (e2@at == qr.l)) {
							fullPath = getTraversalContextNodes();
							caseFound = false;
							for (i <- index(fullPath)) {
								if (!caseFound && Case cf:\case(_,_) := fullPath[i]) {
									cases = cases + cf;
									caseFound = true;
								} else if (caseFound && Stmt sf:\switch(_,_) := fullPath[i]) {
									switches = switches + sf;
									break;
								}
							}
						} 
					}
				}
				
				if (!isEmpty(cases) && !isEmpty(switches)) {
					containingCase = cases[0];
					containingSwitch = switches[0];
					
					// Is this switch useful?
					if (var(name(name(v))) := containingSwitch.cond) {
						possibleCases = reachableCases(c, qr.e, containingSwitch.cases);
						caseValues = { scalar(string(sval)) | \case(someExpr(scalar(string(sval))),_) <- possibleCases };
						varExprs = replaceInExpr(getVariablePart(e), v, caseValues);
						res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) }; 
					} else if (/var(name(name(v))) := containingSwitch.cond) {
						unres = unres + qr.l;
					}
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] assignmentPatternFour(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = assignmentPatternFour(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(earlierPatterns("thirtyfour"),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] antiPatternOne(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return antiPatternOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats antiPatternOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet) {
			set[str] containerVars = { };
			list[Stmt] containingFunctions = [];
			list[ClassItem] containingMethods = [];
			
			Script s = pt[qr.l.top];
			visit(s) {
				case Expr e2 : {
					if ( (e2@at)? && (e2@at == qr.l) ) {
						containingFunctions = [ tcn | Stmt tcn <- getTraversalContextNodes(), tcn is function ];
						containingMethods = [ tcn | ClassItem tcn <- getTraversalContextNodes(), tcn is method ];
					}
				}
			} 
			
			if (size(containingMethods) > 0) {
				containerVars = { pn | param(pn,_,_,_) <- containingMethods[0].params };
			} else if (size(containingFunctions) > 0) {
				containerVars = { pn | param(pn,_,_,_) <- containingFunctions[0].params };
			}
			
			qrVars = { vn | /var(name(name(vn))) := qr.e };
			
			if (size(containerVars & qrVars) > 0) {
				res = res + < qr.l, unknownVar() >;
				if (qr.l in alreadyResolved) {
					unres = unres + qr.l;
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] antiPatternOne(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = antiPatternOne(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(patternOrder(),s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] antiPatternTwo(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return antiPatternTwo(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats antiPatternTwo(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet) {
			qrVars = { vn | /var(name(name(vn))) := qr.e };
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				apAssigns = { };
				visit(carrier(g)) {
					case a:assign(var(name(name(v))),call(_,_)) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:assign(var(name(name(v))),methodCall(_,_,_)) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:assign(var(name(name(v))),staticCall(_,_,_)) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:refAssign(var(name(name(v))),call(_,_)) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:refAssign(var(name(name(v))),methodCall(_,_,_)) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:refAssign(var(name(name(v))),staticCall(_,_,_)) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:assignWOp(var(name(name(v))),call(_,_),_) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:assignWOp(var(name(name(v))),methodCall(_,_,_),_) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}

					case a:assignWOp(var(name(name(v))),staticCall(_,_,_),_) : {
						if (v in qrVars) {
							apAssigns = apAssigns + a;
						}
					}
				}
				
				if (size(apAssigns) > 0) {
					res = res + < qr.l, unknownVar() >;
					if (qr.l in alreadyResolved) {
						unres = unres + qr.l;
					}	
				}
				
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] antiPatternTwo(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = antiPatternTwo(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(patternOrder(),s));
	}
	
	return res;
}

public bool inLocRanges(loc l, set[loc] ls) {
	for (lsi <- ls) {
		if (lsi.offset <= l.offset && (lsi.offset+lsi.length) >= l.offset) return true;
	}
	
	return false;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] antiPatternThree(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return antiPatternThree(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats antiPatternThree(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	tuple[rel[loc,AnalysisName],set[loc]] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { }; set[loc] unres = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet) {
			set[str] containerVars = { };
			list[Stmt] containingFunctions = [];
			list[ClassItem] containingMethods = [];
			qrVars = { vn | /var(name(name(vn))) := qr.e };
			
			Script s = pt[qr.l.top];
			visit(s) {
				case Expr e2 : {
					if ( (e2@at)? && (e2@at == qr.l) ) {
						containingFunctions = [ tcn | Stmt tcn <- getTraversalContextNodes(), tcn is function ];
						containingMethods = [ tcn | ClassItem tcn <- getTraversalContextNodes(), tcn is method ];
					}
				}
			} 
			
			globalDecls = { };
			
			if (size(containingMethods) > 0) {
				globalDecls = { g | /g:global([_*,var(name(name(vn))),_*]) := containingMethods[0].body, vn in qrVars };
			} else if (size(containingFunctions) > 0) {
				globalDecls = { g | /g:global([_*,var(name(name(vn))),_*]) := containingFunctions[0].body, vn in qrVars };
			} else {
				filterLocs = { f@at | /f:function(_,_,_,_) := s } + { m@at | /m:method(_,_,_,_,_) := s };
				globalDecls = { g | /g:global([_*,var(name(name(vn))),_*]) := s, vn in qrVars, !(inLocRanges(g@at,filterLocs))};
			}
						
			if (size(globalDecls) > 0) {
				res = res + < qr.l, unknownVar() >;
				if (qr.l in alreadyResolved) {
					unres = unres + qr.l;
				}
			}
		}
		 
		return < res, unres >;
	}
	 
	< vvusesRes, vvusesUnres > = resolvePattern(vv.vvuses<2>);
	< vvcallsRes, vvcallsUnres > = resolvePattern(vv.vvcalls<2>);
	< vvmcallsRes, vvmcallsUnres > = resolvePattern(vv.vvmcalls<2>);
	< vvnewsRes, vvnewsUnres > = resolvePattern(vv.vvnews<2>);
	< vvpropsRes, vvpropsUnres > = resolvePattern(vv.vvprops<2>);
	< vvcconstsRes, vvcconstsUnres > = resolvePattern(vv.vvcconsts<2>);
	< vvscallsRes, vvscallsUnres > = resolvePattern(vv.vvscalls<2>);
	< vvstargetsRes, vvstargetsUnres > = resolvePattern(vv.vvstargets<2>);
	< vvspropsRes, vvspropsUnres > = resolvePattern(vv.vvsprops<2>);
	< vvsptargetsRes, vvsptargetsUnres > = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), vvusesRes, vvusesUnres),
		resolveStats(size(vvcallsRes<0>), vvcallsRes, vvcallsUnres),
		resolveStats(size(vvmcallsRes<0>), vvmcallsRes, vvmcallsUnres),
		resolveStats(size(vvnewsRes<0>), vvnewsRes, vvnewsUnres),
		resolveStats(size(vvpropsRes<0>), vvpropsRes, vvpropsUnres),
		resolveStats(size(vvcconstsRes<0>), vvcconstsRes, vvcconstsUnres),
		resolveStats(size(vvscallsRes<0>), vvscallsRes, vvscallsUnres),
		resolveStats(size(vvstargetsRes<0>), vvstargetsRes, vvstargetsUnres),
		resolveStats(size(vvspropsRes<0>), vvspropsRes, vvspropsUnres),
		resolveStats(size(vvsptargetsRes<0>), vvsptargetsRes, vvsptargetsUnres));
}

public map[str s, PatternStats p] antiPatternThree(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = antiPatternThree(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs(patternOrder(),s));
	}
	
	return res;
}

public set[Case] reachableCases(CFG g, Expr e, list[Case] cs) {
	ggraph = cfgAsGraph(g);
	flipped = invert(ggraph);

	// Get the expression node(s) that correspond to the starting expression
	startNodes = { gi | gi <- carrier(ggraph), exprNode(ge, _) := gi, (ge@at)?, ge@at == e@at };
	
	// Get just the case expressions on the cases present in this switch/case
	searchExprs = { < ce, ce@at, c > | c:\case(someExpr(ce),_) <- cs };
	
	// Get just the locations of these case expressions
	searchExprLocs = searchExprs<1>;
	
	// Get the CFG nodes that correspond to the case expression nodes
	searchNodes = { gi | gi <- carrier(ggraph), exprNode(ge, _) := gi, (ge@at)?, ge@at in searchExprLocs };

	// Get just the subset of these nodes that are actually reachable from the start nodes if we go backwards
	reachableCaseExprNodes = (flipped*)[startNodes] & searchNodes;
	reachableCaseExprNodeLocs = { rn.expr@at | rn <- reachableCaseExprNodes };
	
	// Get the cases associated with the reachable case expression nodes
	return { c | < _, l, c > <- searchExprs, l in reachableCaseExprNodeLocs };
}

public list[str] patternOrder() {
	return [ "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten", "eleven", "twelve", "thirteen", "fourteen",
			 "twentyone", "twentytwo", "twentythree", "twentyfour", "twentyfive",
			 "thirtyone", "thirtytwo", "thirtythree", "thirtyfour"
		   ];
}

public list[str] earlierPatterns(str s) {
	po = patternOrder();
	if (s in po) {
		return po[..indexOf(po,s)];
	}
	return [];
}

public list[int] getForRange(Stmt f, str v) {
	if (\for([_*,assign(var(name(name(v))),scalar(integer(si))),_*],[_*,cutoff,_*],[_*,incop,_*],_) := f &&
	    (binaryOperation(var(name(name(v))), scalar(integer(si3)), compop) := cutoff) && 
	    (assign(var(name(name(v))),_) := incop || assignWOp(var(name(name(v))),_,_) := incop || unaryOperation(var(name(name(v))),_) := incop) )
	{
		stepsize = 0;
		if ( assign(var(name(name(v))),binaryOperation(var(name(name(v))),scalar(integer(si2)),plus())) := incop ) {
			stepsize = si2;
		} else if ( assign(var(name(name(v))),binaryOperation(var(name(name(v))),scalar(integer(si2)),plus())) := incop ) {
			stepsize = si2;
		} else if ( unaryOperation(var(name(name(v))), preInc()) := incop || unaryOperation(var(name(name(v))), postInc()) := incop) {
			stepsize = 1;
		} else {
			return [ ]; // cannot use it
		}
		if (stepsize == 0) {
			return [ ];
		}
		
		maxnum = 0;
		if ( lt() := compop) {
			maxnum = si3 - 1;
		} else if ( leq() := compop) {
			maxnum = si3;
		} else {
			return [ ];
		}
		if ( maxnum <= si ) {
			return [ ];
		}
		
		return [si,si+stepsize..(maxnum+1)]; 
	}
	
	return [ ];
}

public map[str s, PatternStats p] computeLoopStats(Corpus corpus) {
	pstats = readPatternStats("one");
	pstats = addPatternStats(pstats,readPatternStats("two"));	
	pstats = addPatternStats(pstats,readPatternStats("three"));	
	pstats = addPatternStats(pstats,readPatternStats("four"));	
	pstats = addPatternStats(pstats,readPatternStats("five"));	
	pstats = addPatternStats(pstats,readPatternStats("six"));	
	pstats = addPatternStats(pstats,readPatternStats("seven"));	
	pstats = addPatternStats(pstats,readPatternStats("eight"));	
	pstats = addPatternStats(pstats,readPatternStats("nine"));	
	pstats = addPatternStats(pstats,readPatternStats("ten"));	
	pstats = addPatternStats(pstats,readPatternStats("eleven"));	
	pstats = addPatternStats(pstats,readPatternStats("twelve"));	
	pstats = addPatternStats(pstats,readPatternStats("thirteen"));	
	pstats = addPatternStats(pstats,readPatternStats("fourteen"));	
	//alreadyResolved= ( s : patternResolvedLocs(earlierPatterns("twentyone"),s) | s <- corpus );
	//pstats = fixPatternStats(pstats, alreadyResolved); 	
	return pstats;
}

public void writeLoopStats(Corpus corpus) {
	pstatsLoops = computeLoopStats(corpus);
	paperLoc = |home:///Dropbox/Papers/2015/var-feature-resolution/|;
	writeFile(paperLoc+"vv-pattern-loops.tex", patternResultsAsLatex(pstatsLoops,"loops",corpus));
}

public map[str s, PatternStats p] computeAssignmentStats(Corpus corpus) {
	pstats = readPatternStats("twentyone");	
	pstats = addPatternStats(pstats,readPatternStats("twentytwo"));	
	pstats = addPatternStats(pstats,readPatternStats("twentythree"));	
	pstats = addPatternStats(pstats,readPatternStats("twentyfour"));	
	//alreadyResolved= ( s : patternResolvedLocs(earlierPatterns("thirtyone"),s) | s <- corpus );
	//pstats = fixPatternStats(pstats, alreadyResolved); 	
	return pstats;
}

public void writeAssignmentStats(Corpus corpus) {
	pstatsAssignments = computeAssignmentStats(corpus);
	paperLoc = |home:///Dropbox/Papers/2015/var-feature-resolution/|;
	writeFile(paperLoc+"vv-pattern-assignments.tex", patternResultsAsLatex(pstatsAssignments,"assignments",corpus));
}

public map[str s, PatternStats p] computeFlowStats(Corpus corpus) {
	pstats = readPatternStats("thirtyone");	
	pstats = addPatternStats(pstats,readPatternStats("twentyfive"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtytwo"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtythree"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtyfour"));	
	//alreadyResolved= ( s : patternResolvedLocs(patternOrder(),s) | s <- corpus );
	//pstats = fixPatternStats(pstats, alreadyResolved); 	
	return pstats;
}

public void writeFlowStats(Corpus corpus) {
	pstatsFlow = computeFlowStats(corpus);
	paperLoc = |home:///Dropbox/Papers/2015/var-feature-resolution/|;
	writeFile(paperLoc+"vv-pattern-flow.tex", patternResultsAsLatex(pstatsFlow,"flow",corpus));
}
	
public map[str s, PatternStats p] computeAllStats(Corpus corpus) {
	pstats = readPatternStats("one");
	pstats = addPatternStats(pstats,readPatternStats("two"));	
	pstats = addPatternStats(pstats,readPatternStats("three"));	
	pstats = addPatternStats(pstats,readPatternStats("four"));	
	pstats = addPatternStats(pstats,readPatternStats("five"));	
	pstats = addPatternStats(pstats,readPatternStats("six"));	
	pstats = addPatternStats(pstats,readPatternStats("seven"));	
	pstats = addPatternStats(pstats,readPatternStats("eight"));	
	pstats = addPatternStats(pstats,readPatternStats("nine"));	
	pstats = addPatternStats(pstats,readPatternStats("ten"));	
	pstats = addPatternStats(pstats,readPatternStats("eleven"));	
	pstats = addPatternStats(pstats,readPatternStats("twelve"));	
	pstats = addPatternStats(pstats,readPatternStats("thirteen"));	
	pstats = addPatternStats(pstats,readPatternStats("fourteen"));	
	pstats = addPatternStats(pstats,readPatternStats("twentyone"));	
	pstats = addPatternStats(pstats,readPatternStats("twentytwo"));	
	pstats = addPatternStats(pstats,readPatternStats("twentythree"));	
	pstats = addPatternStats(pstats,readPatternStats("twentyfour"));	
	pstats = addPatternStats(pstats,readPatternStats("twentyfive"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtyone"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtytwo"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtythree"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtyfour"));
	
	//alreadyResolved= ( s : patternResolvedLocs(patternOrder(),s) | s <- corpus );
	//pstats = fixPatternStats(pstats, alreadyResolved); 	
	return pstats;
}

public void writeAllStats(Corpus corpus) {
	pstatsAll = computeAllStats(corpus);
	paperLoc = |home:///Dropbox/Papers/2015/var-feature-resolution/|;
	writeFile(paperLoc+"vv-pattern-all.tex", patternResultsAsLatexForAll(pstatsAll,"all",corpus));
}

public map[str s, PatternStats p] computeAntiStats(Corpus corpus) {
	pstats = readPatternStats("antione");	
	pstats = addPatternStats(pstats,readPatternStats("antitwo"), fixUnresolved = false);	
	pstats = addPatternStats(pstats,readPatternStats("antithree"), fixUnresolved = false);	
	return pstats;
}

public void writeAntiStats(Corpus corpus) {
	pstatsAnti = computeAntiStats(corpus);
	paperLoc = |home:///Dropbox/Papers/2015/var-feature-resolution/|;
	writeFile(paperLoc+"vv-pattern-anti.tex", patternResultsAsLatex(pstatsAnti,"anti",corpus));
}

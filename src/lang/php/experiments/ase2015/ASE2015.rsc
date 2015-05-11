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
		return "Product & Files & \\multicolumn{19}{c}{PHP Variable Features} \\\\
		       '\\cmidrule{3-21}
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
public default bool hasVariableForName(Expr e) = false;

public str getVariableName(var(expr(var(name(name(str s)))))) = s;
public str getVariableName(call(expr(var(name(name(str s)))),_)) = s;
public str getVariableName(methodCall(_,expr(var(name(name(str s)))),_)) = s;
public str getVariableName(new(expr(var(name(name(str s)))),_)) = s;
public str getVariableName(propertyFetch(_,expr(var(name(name(str s)))))) = s;
public str getVariableName(staticCall(_,expr(var(name(name(str s)))),_)) = s;
public str getVariableName(staticCall(expr(var(name(name(str s)))),_,_)) = s;
public str getVariableName(staticPropertyFetch(expr(var(name(name(str s)))),_)) = s;
public default str getVariableName(Expr e) { throw "No variable name found"; }

public Expr getVariablePart(var(expr(Expr e))) = e;
public Expr getVariablePart(call(expr(Expr e),_)) = e;
public Expr getVariablePart(methodCall(_,expr(Expr e),_)) = e;
public Expr getVariablePart(new(expr(Expr e),_)) = e;
public Expr getVariablePart(propertyFetch(_,expr(Expr e))) = e;
public Expr getVariablePart(staticCall(_,expr(Expr e),_)) = e;
public Expr getVariablePart(staticCall(expr(Expr e),_,_)) = e;
public Expr getVariablePart(staticPropertyFetch(expr(Expr e),_)) = e;
public default Expr getVariablePart(Expr e) { throw "No variable name found"; }

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

public set[str] gatherAssignedStrings(CFG g, Expr e) {
	return { getScalarString(e2) | exprNode(assign(e, e2),_) <- g.nodes, exprIsScalarString(e2) };
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

data ResolveStats = resolveStats(int resolved, int total, rel[loc,AnalysisName] resolvedLocs);

public ResolveStats addResolveStats(ResolveStats r1, ResolveStats r2) {
	r1.resolved = r1.resolved + r2.resolved;
	r1.resolvedLocs = r1.resolvedLocs + r2.resolvedLocs;
	return r1;
}

data PatternStats = patternStats(ResolveStats vvuses, ResolveStats vvcalls, ResolveStats vvmcalls, ResolveStats vvnews, ResolveStats vvprops,
								 ResolveStats vvcconsts, ResolveStats vvscalls, ResolveStats vvstargets, ResolveStats vvsprops, ResolveStats vvsptargets);

public PatternStats addPatternStats(PatternStats p1, PatternStats p2) {
	return patternStats(addResolveStats(p1.vvuses, p2.vvuses), addResolveStats(p1.vvcalls, p2.vvcalls),
						addResolveStats(p1.vvmcalls, p2.vvmcalls), addResolveStats(p1.vvnews, p2.vvnews),
						addResolveStats(p1.vvprops, p2.vvprops), addResolveStats(p1.vvcconsts, p2.vvcconsts),
						addResolveStats(p1.vvscalls, p2.vvscalls), addResolveStats(p1.vvstargets, p2.vvstargets),
						addResolveStats(p1.vvsprops, p2.vvsprops), addResolveStats(p1.vvsptargets, p2.vvsptargets));
}

public map[str s, PatternStats p] addPatternStats(map[str s, PatternStats p] p1, map[str s, PatternStats p] p2) {
	return (s : addPatternStats(p1[s],p2[s]) | s <- p1 );
}

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
								println("Dangerous use, used with reference parameter at <du@at>: <pp(du)>");
								return true;
							}
						} else {
							println("Dangerous use, unknown function found at <du@at>: <pp(du)>");
							return true;
						}
					}
				} else {
					println("Dangerous use, unknown call, found at <du@at>: <pp(du)>");
					return true;
				}
				println("Safe use in call at <du@at>: <pp(du)>");
				return false;
			}
		}

		case du:methodCall(_,mt,plist) : {
			if (du@at notin ignoreLocs) {
				if (name(name(mn)) := mt) {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						if (mn in fm.methods<0>) {
							mnMatches = fm.methods[mn];
							for (mnMatch <- mnMatches, size(mnMatch) >= (idx+1), mnMatch[idx].isRef) {
								println("Dangerous use, used with reference parameter at <du@at>: <pp(du)>");
								return true;
							}
						} else {
							println("Dangerous use, unknown function found at <du@at>: <pp(du)>");
							return true;
						}
					}
				} else {
					println("Dangerous use, unknown call, found at <du@at>: <pp(du)>");
					return true;
				}
				println("Safe use in call at <du@at>: <pp(du)>");
				return false;
			}
		}

		case du:staticCall(_,mt,plist) : {
			if (du@at notin ignoreLocs) {
				if (name(name(mn)) := mt) {
					for (idx <- index(plist), actualParameter(var(name(name(v))),_) := plist[idx]) {
						if (mn in fm.methods<0>) {
							mnMatches = fm.methods[mn];
							for (mnMatch <- mnMatches, size(mnMatch) >= (idx+1), mnMatch[idx].isRef) {
								println("Dangerous use, used with reference parameter at <du@at>: <pp(du)>");
								return true;
							}
						} else {
							println("Dangerous use, unknown function found at <du@at>: <pp(du)>");
							return true;
						}
					}
				} else {
					println("Dangerous use, unknown call, found at <du@at>: <pp(du)>");
					return true;
				}
				println("Safe use in call at <du@at>: <pp(du)>");
				return false;
			}
		}
	}
	
	return false;
}

public bool addressTaken(Stmt s, str v) {
	return false;
}

@doc{
	Resolve variable definitions for Pattern One. Pattern one is the following:
	
	1. A foreach loop is defined that works directly over a literal array
	2. Each element of this array is assigned into the foreach variable
	3. This foreach variable is used directly as the name of the variable being accessed
	
	We can resolve this under the restriction that the foreach variable is not used
	in a way where it could be modified (it is not passed to a function or method
	as a reference parameter, it is not reference assigned to another variable, it
	is not used as the target of an assignment). This also needs to occur in the
	// context of the foreach that provides the variable.
}
public rel[loc,AnalysisName] patternOne(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats patternOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features
	vvAll = collapseVVInfo(vv);
	
	// Get back the script locations for all the uses
	scriptLocs = { qr.l.top | qr <- vvAll };
	//println("Found variable features in <size(scriptLocs)> files");
	
	// Generate control flow graphs for each script location
	//map[loc,map[NamePath,CFG]] scriptCFGs = ( l : buildCFGs(pt[l],buildBasicBlocks=false) | l <- scriptLocs );

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			//println("Processing expression <pp(e)> at location <qr.l>");
			//CFG c = cfgForExpression(scriptCFGs[qr.l.top],e);
			//g = cfgAsGraph(c);
			
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
					println("Cannot use foreach, it creates an alias, <fe@at>");
				} else {
					aexp = fe.arrayExpr;
					if (array(aelist) := aexp && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
						if (hasDangerousUse(fe, v, fm)) {
							println("Cannot use foreach, it has a potentially dangerous use, <fe@at>");
						} else {
							res = res + { < qr.l, varName(getScalarString(aeItem.val)) > | aeItem <- aelist };
						}
					} else {
						println("Array expression <pp(aexp)> does not match pattern 1, <qr.l>");
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternOne(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternOne(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt));
	}
	
	return res;
}

rel[loc,Expr] getStandardAssignmentsFor(str varname, set[CFGNode] nodes) {
	return { < e@at, e > | exprNode(e:assign(var(name(name(varname))),_),_) <- nodes };
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] patternTwo(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternTwo(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternTwo(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getVariableName(e);
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case e : {
						if (e@at == qr.l) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("Cannot use foreach, it creates an alias, <fe@at>");
					} else {
						aexp = fe.arrayExpr;
						if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
							// TODO: Verify reachability
							assignments = getStandardAssignmentsFor(aname, carrier(g));
							if (size(assignments<1>) == 1) {
								assignLocs = assignments<0>;
								assignExpr = getOneFrom(assignments<1>);						
								if (array(aelist) := assignExpr.assignExpr && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
									if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
										println("Cannot use foreach, it has a potentially dangerous use");
									} else {
										res = res + { < qr.l, varName(getScalarString(aeItem.val)) > | aeItem <- aelist };
									}
								} else {
									println("Array expression <pp(aexp)> at <aexp@at> does not match pattern 2, <qr.l>");
								}
							} else if (isEmpty(assignments<1>)) {
								println("No local assignments, cannot use variable <aname>, <qr.l>");
							} else {
								println("Inconsistent assignments, cannot use variable <aname>, <qr.l>");
							}							
						} else {
							println("Array expression in foreach <pp(aexp)> does not match pattern 2, <qr.l>");
						}
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternTwo(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternTwo(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs("one",s));
	}
	
	return res;
}


@doc{
	Resolve variable definitions for Pattern One. Pattern one is the following:
	
	1. A foreach loop is defined that works directly over a literal array
	2. Each element of this array is assigned into the foreach variable
	3. This foreach variable is used directly as the name of the variable being accessed
	
	We can resolve this under the restriction that the foreach variable is not used
	in a way where it could be modified (it is not passed to a function or method
	as a reference parameter, it is not reference assigned to another variable, it
	is not used as the target of an assignment). This also needs to occur in the
	// context of the foreach that provides the variable.
}
public rel[loc,AnalysisName] patternThree(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternThree(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}


public PatternStats patternThree(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features
	vvAll = collapseVVInfo(vv);
	
	// Get back the script locations for all the uses
	scriptLocs = { qr.l.top | qr <- vvAll };
	//println("Found variable features in <size(scriptLocs)> files");
	
	// Generate control flow graphs for each script location
	//map[loc,map[NamePath,CFG]] scriptCFGs = ( l : buildCFGs(pt[l],buildBasicBlocks=false) | l <- scriptLocs );

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			//println("Processing expression <pp(e)> at location <qr.l>");
			//CFG c = cfgForExpression(scriptCFGs[qr.l.top],e);
			//g = cfgAsGraph(c);
			
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
					println("Cannot use foreach, it creates an alias, <fe@at>");
				} else {
					aexp = fe.arrayExpr;
					if (array(aelist) := aexp && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {
						if (hasDangerousUse(fe, v, fm)) {
							println("Cannot use foreach, it has a potentially dangerous use, <fe@at>");
						} else {
							res = res + { < qr.l, varName(getScalarString(aeItem.key.expr)) > | aeItem <- aelist };
						}
					} else {
						println("Array expression <pp(aexp)> does not match pattern 3, <qr.l>");
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternThree(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternThree(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two"},s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] patternFour(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternFour(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternFour(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str v = getVariableName(e);
				
				// Find the node inside the system using a visit, that way we can also
				// find the containing foreach
				Script s = pt[qr.l.top];
				list[Stmt] foreaches = [];
				visit(s) {
					case e : {
						if (e@at == qr.l) {
							foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,someExpr(var(name(name(v)))),_,_,_) := cn ];
						} 
					}
				}
				
				if (!isEmpty(foreaches)) {
					fe = foreaches[0];
					if (fe.byRef) {
						println("Cannot use foreach, it creates an alias, <fe@at>");
					} else {
						aexp = fe.arrayExpr;
						if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
							// TODO: Verify reachability
							assignments = getStandardAssignmentsFor(aname, carrier(g));
							if (size(assignments<1>) == 1) {
								assignLocs = assignments<0>;
								assignExpr = getOneFrom(assignments<1>);			
								if (array(aelist) := assignExpr.assignExpr && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {			
									if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
										println("Cannot use foreach, it has a potentially dangerous use");
									} else {
										res = res + { < qr.l, varName(getScalarString(aeItem.key.expr)) > | aeItem <- aelist };
									}
								} else {
									println("Array expression <pp(aexp)> at <aexp@at> does not match pattern 4, <qr.l>");
								}
							} else if (isEmpty(assignments<1>)) {
								println("No local assignments, cannot use variable <aname>, <qr.l>");
							} else {
								println("Inconsistent assignments, cannot use variable <aname>, <qr.l>");
							}							
						} else {
							println("Array expression in foreach <pp(aexp)> does not match pattern 4, <qr.l>");
						}
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternFour(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternFour(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three"},s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] patternFive(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternFive(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternFive(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			if (/install/ := qr.l.path) {
				println("Found it");
			}			
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// TODO: Here, we need to check to see if this is a combination of just
					// string literals and a single variable -- the easiest way to do that
					// will be to see if there is a single variable, find the possible
					// values, and then try to solve it

					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case e : {
							if (e@at == qr.l) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("Cannot use foreach, it creates an alias, <fe@at>");
						} else {
							aexp = fe.arrayExpr;
							if (array(aelist) := aexp && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
								if (hasDangerousUse(fe, v, fm)) {
									println("Cannot use foreach, it has a potentially dangerous use");
								} else {
									varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.val | aeItem <- aelist }); 
									res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
								}
							} else {
								println("Array expression <pp(aexp)> at <aexp@at> does not match pattern 7, <qr.l>");
							}
						}
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternFive(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternFive(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four"},s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] patternSix(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternSix(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternSix(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			if (/install/ := qr.l.path) {
				println("Found it");
			}			
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// TODO: Here, we need to check to see if this is a combination of just
					// string literals and a single variable -- the easiest way to do that
					// will be to see if there is a single variable, find the possible
					// values, and then try to solve it

					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case e : {
							if (e@at == qr.l) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("Cannot use foreach, it creates an alias, <fe@at>");
						} else {
							aexp = fe.arrayExpr;
							if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
								// TODO: Verify reachability
								assignments = getStandardAssignmentsFor(aname, carrier(g));
								if (size(assignments<1>) == 1) {
									assignLocs = assignments<0>;
									assignExpr = getOneFrom(assignments<1>);						
									if (array(aelist) := assignExpr.assignExpr && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
										if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
											println("Cannot use foreach, it has a potentially dangerous use");
										} else {
											varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.val | aeItem <- aelist }); 
											res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
										}
									} else {
										println("Array expression <pp(aexp)> at <aexp@at> does not match pattern 8, <qr.l>");
									}
								} else if (isEmpty(assignments<1>)) {
									println("No local assignments, cannot use variable <aname>, <qr.l>");
								} else {
									println("Inconsistent assignments, cannot use variable <aname>, <qr.l>");
								}							
							} else {
								println("Array expression in foreach <pp(aexp)> does not match pattern 8, <qr.l>");
							}
						}
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternSix(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternSix(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four","five"},s));
	}
	
	return res;
}


public rel[loc,AnalysisName] patternSeven(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternSeven(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternSeven(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			if (/getid3/ := qr.l.path) {
				println("Found it");
			}			
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// TODO: Here, we need to check to see if this is a combination of just
					// string literals and a single variable -- the easiest way to do that
					// will be to see if there is a single variable, find the possible
					// values, and then try to solve it

					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case e : {
							if (e@at == qr.l) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,someExpr(var(name(name(v)))),_,_,_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("Cannot use foreach, it creates an alias, <fe@at>");
						} else {
							aexp = fe.arrayExpr;
							if (array(aelist) := aexp && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {
								if (hasDangerousUse(fe, v, fm)) {
									println("Cannot use foreach, it has a potentially dangerous use");
								} else {
									varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.key.expr | aeItem <- aelist }); 
									res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
								}
							} else {
								println("Array expression <pp(aexp)> at <aexp@at> does not match pattern 7, <qr.l>");
							}
						}
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternSeven(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternSeven(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four","five","six"},s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern One. Pattern one is the following:
	
	1. A foreach loop is defined that works directly over a literal array
	2. Each element of this array is assigned into the foreach variable
	3. This foreach variable is used directly as the name of the variable being accessed
	
	We can resolve this under the restriction that the foreach variable is not used
	in a way where it could be modified (it is not passed to a function or method
	as a reference parameter, it is not reference assigned to another variable, it
	is not used as the target of an assignment). This also needs to occur in the
	// context of the foreach that provides the variable.
}
public rel[loc,AnalysisName] patternEight(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternEight(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternEight(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			if (/options/ := qr.l.path) {
				println("Found it");
			}
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(e)> at <e@at>");
			} else {
				g = cfgAsGraph(c);
				
				// We have a variable feature use, so get the actual variable used to hold it
				str av = getVariableName(e);
				avAssign = getStandardAssignmentsFor(av, carrier(g));
				if (size(avAssign<1>) == 1 && containsSingleVar(getOneFrom(avAssign<1>), toIgnore = {av})) {
					avAssignExpr = getOneFrom(avAssign<1>);
					v = getSingleVar(avAssignExpr, toIgnore = {av});
	
					// TODO: Here, we need to check to see if this is a combination of just
					// string literals and a single variable -- the easiest way to do that
					// will be to see if there is a single variable, find the possible
					// values, and then try to solve it

					// Find the node inside the system using a visit, that way we can also
					// find the containing foreach
					Script s = pt[qr.l.top];
					list[Stmt] foreaches = [];
					visit(s) {
						case e : {
							if (e@at == qr.l) {
								foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,some(var(name(name(v)))),_,_,_) := cn ];
							} 
						}
					}
					
					if (!isEmpty(foreaches)) {
						fe = foreaches[0];
						if (fe.byRef) {
							println("Cannot use foreach, it creates an alias, <fe@at>");
						} else {
							aexp = fe.arrayExpr;
							if (var(name(name(aname))) := aexp || cast(array(),var(name(name(aname)))) := aexp) {
								// TODO: Verify reachability
								assignments = getStandardAssignmentsFor(aname, carrier(g));
								if (size(assignments<1>) == 1) {
									assignLocs = assignments<0>;
									assignExpr = getOneFrom(assignments<1>);						
									if (array(aelist) := assignExpr.assignExpr && false notin { aeItem.key is someExpr | aeItem <- aelist } && false notin { exprIsScalarString(aeItem.key.expr) | aeItem <- aelist }) {
										if (hasDangerousUse(fe, v, fm, ignoreLocs=assignLocs)) {
											println("Cannot use foreach, it has a potentially dangerous use");
										} else {
											varExprs = replaceInExpr(avAssignExpr.assignExpr, v, { aeItem.key.expr | aeItem <- aelist }); 
											res = res + { < qr.l, varName(getScalarString(ve)) > | ve <- varExprs, exprIsScalarString(ve) };
										}
									} else {
										println("Array expression <pp(aexp)> at <aexp@at> does not match pattern 10, <qr.l>");
									}
								} else if (isEmpty(assignments<1>)) {
									println("No local assignments, cannot use variable <aname>, <qr.l>");
								} else {
									println("Inconsistent assignments, cannot use variable <aname>, <qr.l>");
								}							
							} else {
								println("Array expression in foreach <pp(aexp)> does not match pattern 10, <qr.l>");
							}
						}
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternEight(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternEight(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four","five","six","seven"},s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] patternTwentyOne(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternTwentyOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternTwentyOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				try {
					vp = getVariablePart(qr.e);
					if (propertyFetch(_,name(name(s))) := vp) {
						if (definitePropertyAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStrings(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						}
					} else if (var(name(name(s))) := vp) {
						if (definiteVariableAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStrings(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						}
					}
				} catch _ : {
					continue;
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternTwentyOne(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternTwentyOne(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four","five","six","seven","eight"},s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] patternTwentyTwo(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternTwentyTwo(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternTwentyTwo(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet,  qr.l notin alreadyResolved) {
			CFG c = loadCFG(findMapEntry(scriptCFGs[qr.l.top], qr.l));
			
			if (emptyCFG() := c) {
				println("WARNING: No CFG found for <pp(qr.e)> at <qr.e@at>");
			} else {
				try {
					vp = getVariablePart(qr.e);
					if (propertyFetch(_,name(name(s))) := vp) {
						if (definitePropertyAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStrings2(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						}
					} else if (var(name(name(s))) := vp) {
						if (definiteVariableAssignment(c, s, qr.e)) {
							assigned = gatherAssignedStrings2(c, vp);
							res = res + { < qr.l, varName(as) > | as <- assigned };
						}
					}
				} catch _ : {
					continue;
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternTwentyTwo(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternTwentyTwo(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four","five","six","seven","eight","twentyOne"},s));
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
		writeBinaryValueFile(dataLoc + "<s>-<corpus[s]>.vvinfo", vv);
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
	writeBinaryValueFile(resultLoc + "pattern-<pname>.bin", stats);
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
		{ < mn, pi > | /functionSig([_*,method(mn)], list[ParamInfo] pi) := sysSignatures } +
		{ < mn, plist2pilist(plist) > | methodSummary([_*,function(fn)],_,plist,_,_,_,_) <- msum };
		
	return fmParamInfo(functions, methods);
}

private loc functionInfoLoc = baseLoc + "serialized/functionInfo";

public void writeFunctionInfo(Corpus corpus, str s, FMParamInfo fp) {
	writeBinaryValueFile(functionInfoLoc + "<s>-<corpus[s]>.finfo", fp);
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
		return "Product & Files & \\multicolumn{17}{c}{Resolved Variable Features, Pattern <pname>} \\\\
		       '\\cmidrule{3-19}
		       ' & & \\multicolumn{2}{c}{Variables} & \\phantom{a} & \\multicolumn{2}{c}{Function Calls} & \\phantom{a} & \\multicolumn{2}{c}{Method Calls} & \\phantom{a} & \\multicolumn{2}{c}{Property Fetches} & \\phantom{a} & \\multicolumn{2}{c}{Instantiations} & \\phantom{a} & \\multicolumn{2}{c}{All} \\\\
		       '\\cmidrule{3-4} \\cmidrule{6-7} \\cmidrule{9-10} \\cmidrule{12-13} \\cmidrule{15-16} \\cmidrule{18-19}
		       ' &  & Resolved & Uses && Resolved & Uses && Resolved & Uses && Resolved & Uses && Resolved & Uses && Resolved & Uses \\\\ \\midrule";
	}
	
	str c(ResolveStats vv) = "\\numprint{<vv.resolved>} & \\numprint{<vv.total>}";
	
//data ResolveStats = resolveStats(int resolved, int total, rel[loc,AnalysisName] resolvedLocs);
//
//data PatternStats = patternStats(ResolveStats vvuses, ResolveStats vvcalls, ResolveStats vvmcalls, ResolveStats vvnews, ResolveStats vvprops,
//								 ResolveStats vvcconsts, ResolveStats vvscalls, ResolveStats vvstargets, ResolveStats vvsprops, ResolveStats vvsptargets);
	
	int allResolved(str p) = pstats[p].vvuses.resolved + pstats[p].vvcalls.resolved + pstats[p].vvmcalls.resolved + pstats[p].vvnews.resolved + pstats[p].vvprops.resolved +
		pstats[p].vvcconsts.resolved + pstats[p].vvscalls.resolved + pstats[p].vvstargets.resolved + pstats[p].vvsprops.resolved + pstats[p].vvsptargets.resolved;

	int allUses(str p) = pstats[p].vvuses.total + pstats[p].vvcalls.total + pstats[p].vvmcalls.total + pstats[p].vvnews.total + pstats[p].vvprops.total +
		pstats[p].vvcconsts.total + pstats[p].vvscalls.total + pstats[p].vvstargets.total + pstats[p].vvsprops.total + pstats[p].vvsptargets.total;
		
	str productLine(str p) {
		< lineCount, fileCount > = getOneFrom(ci[p,corpus[p]]);
		return "<p> & \\numprint{<fileCount>} & <c(pstats[p].vvuses)> && <c(pstats[p].vvcalls)> && <c(pstats[p].vvmcalls)> && <c(pstats[p].vvprops)> && <c(pstats[p].vvnews)> && \\numprint{<allResolved(p)>} & \\numprint{<allUses(p)>} \\\\";
	}

	res = "\\npaddmissingzero
		  '\\npfourdigitsep
		  '\\begin{table*}
		  '\\centering
		  '\\caption{PHP Variable Features Resolved By Pattern <pname>.\\label{table-var-pattern-<pname>}}
		  '\\ra{1.0}
		  '\\resizebox{\\textwidth}{!}{%
		  '\\begin{tabular}{@{}lrrrcrrcrrcrrcrrcrr@{}} \\toprule 
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
					writeBinaryValueFile(ci.forTopLevel, scriptCFGs[np]);
				} else {
					toWrite = cfgLoc + "cfg-<uniqueIds>.bin";				
					uniqueIds = uniqueIds + 1;
					writeBinaryValueFile(toWrite, scriptCFGs[np]);
					ci.forContainers[scriptCFGs[np].at] = toWrite;
				}
			}
			infoMap[l] = ci; 
		}
		writeBinaryValueFile(cfgLoc+"<s>-<corpus[s]>.cfgmap", infoMap);
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

public bool definiteVariableAssignment(CFG g, str v, Expr usedBy) {
	set[CFGNode] checked = { };
	ggraph = cfgAsGraph(g);
	
	bool assignedOnPath(CFGNode n) {
		// If we reach an exit node it doesn't matter, that means we have a path
		// where we don't have a definition but we also don't have a use.
		if (isExitNode(n)) return true;

		// If we find a use of the expression this means we have the use before the def
		if (exprNode(e,_) := n && e == usedBy && e@at == usedBy@at) return false;

		if (exprNode(assign(var(name(name(v))),_),_) := n) return true;
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

public bool definitePropertyAssignment(CFG g, str v, Expr usedBy) {
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

		if (exprNode(assign(propertyFetch(_,name(name(v))),_),_) := n) return true;
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

public void runExtracts() {
	corpus = getBaseCorpus();
	extractVVInfo(corpus);
	extractFunctionInfo(corpus);	
	extractCFGs(corpus);	
}

public void runPatterns() {
	corpus = getBaseCorpus();
	println("Running Pattern One");
	writePatternStats("one", patternOne(corpus));

	println("Running Pattern Two");
	writePatternStats("two", patternTwo(corpus));

	println("Running Pattern Three");
	writePatternStats("three", patternThree(corpus));

	println("Running Pattern Four");
	writePatternStats("four", patternFour(corpus));

	println("Running Pattern Five");
	writePatternStats("five", patternFive(corpus));

	println("Running Pattern Six");
	writePatternStats("six", patternSix(corpus));

	println("Running Pattern Seven");
	writePatternStats("seven", patternSeven(corpus));

	println("Running Pattern Eight");
	writePatternStats("eight", patternEight(corpus));

	println("Running Pattern Twenty One");
	writePatternStats("twentyone", patternTwentyOne(corpus));

	println("Running Pattern Twenty Two");
	writePatternStats("twentytwo", patternTwentyTwo(corpus));
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

	writeFile(paperLoc+"vv-pattern-twenty-one.tex", patternResultsAsLatex(readPatternStats("twentyone"), "twentyone", corpus));	
	writeFile(paperLoc+"vv-pattern-twenty-two.tex", patternResultsAsLatex(readPatternStats("twentytwo"), "twentytwo", corpus));
	
	writeFile(paperLoc+"vv-pattern-thirty-one.tex", patternResultsAsLatex(readPatternStats("thirtyone"), "thirtyone", corpus));
	writeFile(paperLoc+"vv-pattern-thirty-two.tex", patternResultsAsLatex(readPatternStats("thirtytwo"), "thirtytwo", corpus));

	pstats = readPatternStats("one");
	pstats = addPatternStats(pstats,readPatternStats("two"));	
	pstats = addPatternStats(pstats,readPatternStats("three"));	
	pstats = addPatternStats(pstats,readPatternStats("four"));	
	pstats = addPatternStats(pstats,readPatternStats("five"));	
	pstats = addPatternStats(pstats,readPatternStats("six"));	
	pstats = addPatternStats(pstats,readPatternStats("seven"));	
	pstats = addPatternStats(pstats,readPatternStats("eight"));	

	pstats = addPatternStats(pstats,readPatternStats("twentyone"));	
	pstats = addPatternStats(pstats,readPatternStats("twentytwo"));	

	pstats = addPatternStats(pstats,readPatternStats("thirtyone"));	
	pstats = addPatternStats(pstats,readPatternStats("thirtytwo"));	

	writeFile(paperLoc+"vv-pattern-all.tex", patternResultsAsLatex(pstats,"all",corpus));
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
public rel[loc,AnalysisName] patternThirtyOne(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternThirtyOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternThirtyOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
		// Grab back the proper control flow graph for a given location
		for (qr <- qrSet, qr.l notin alreadyResolved, e := qr.e, hasVariableForName(e)) {
			//println("Processing expression <pp(e)> at location <qr.l>");
			//CFG c = cfgForExpression(scriptCFGs[qr.l.top],e);
			//g = cfgAsGraph(c);
			
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
					} else {
						println("Conditional expression <pp(cond)> is not useful, no match at <qr.l>");
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternThirtyOne(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternThirtyOne(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four","five","six","seven","eight","twentyOne","twentyTwo"},s));
	}
	
	return res;
}

@doc{
	Resolve variable definitions for Pattern Two. Pattern two is like pattern one, but the array may be defined outside of the foreach.
}
public rel[loc,AnalysisName] patternThirtyTwo(str system, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	return patternThirtyTwo(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt, alreadyResolved = alreadyResolved);
}

public PatternStats patternThirtyTwo(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing(), set[loc] alreadyResolved = { }) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
	// Load info on functions
	fm = readFunctionInfo(corpus, system);
	
	// Collapse all the var features into one set
	vvAll = collapseVVInfo(vv);
	
	// Load the CFG information map so we can get back generated CFGs
	scriptCFGs = loadCFGMap(corpus, system);

	rel[loc,AnalysisName] resolvePattern(list[QueryResult] qrSet) {
		rel[loc,AnalysisName] res = { };
			
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
					}
				}
			}
		}
		 
		return res;
	}
	 
	vvusesRes = resolvePattern(vv.vvuses<2>);
	vvcallsRes = resolvePattern(vv.vvcalls<2>);
	vvmcallsRes = resolvePattern(vv.vvmcalls<2>);
	vvnewsRes = resolvePattern(vv.vvnews<2>);
	vvpropsRes = resolvePattern(vv.vvprops<2>);
	vvcconstsRes = resolvePattern(vv.vvcconsts<2>);
	vvscallsRes = resolvePattern(vv.vvscalls<2>);
	vvstargetsRes = resolvePattern(vv.vvstargets<2>);
	vvspropsRes = resolvePattern(vv.vvsprops<2>);
	vvsptargetsRes = resolvePattern(vv.vvsptargets<2>);
	
	return patternStats(
		resolveStats(size(vvusesRes<0>), size(vv.vvuses<2>), vvusesRes),
		resolveStats(size(vvcallsRes<0>), size(vv.vvcalls<2>), vvcallsRes),
		resolveStats(size(vvmcallsRes<0>), size(vv.vvmcalls<2>), vvmcallsRes),
		resolveStats(size(vvnewsRes<0>), size(vv.vvnews<2>), vvnewsRes),
		resolveStats(size(vvpropsRes<0>), size(vv.vvprops<2>), vvpropsRes),
		resolveStats(size(vvcconstsRes<0>), size(vv.vvcconsts<2>), vvcconstsRes),
		resolveStats(size(vvscallsRes<0>), size(vv.vvscalls<2>), vvscallsRes),
		resolveStats(size(vvstargetsRes<0>), size(vv.vvstargets<2>), vvstargetsRes),
		resolveStats(size(vvspropsRes<0>), size(vv.vvsprops<2>), vvspropsRes),
		resolveStats(size(vvsptargetsRes<0>), size(vv.vvsptargets<2>), vvsptargetsRes));
}

public map[str s, PatternStats p] patternThirtyTwo(Corpus corpus) {
	map[str s, PatternStats p] res = ( );
	
	for (s <- corpus) {
		pt = loadBinary(s, corpus[s]);
		res[s] = patternThirtyTwo(corpus, s, loadVVInfo(getBaseCorpus(), s), ptopt = just(pt), alreadyResolved=patternResolvedLocs({"one","two","three","four","five","six","seven","eight","twentyOne","twentyTwo"},s));
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
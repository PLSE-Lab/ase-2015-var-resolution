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
import lang::php::analysis::cfg::BuildCFG;
import lang::php::analysis::NamePaths;
import lang::php::analysis::evaluators::AlgebraicSimplification;
import lang::php::analysis::names::AnalysisNames;

import IO;
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
public void buildCorpus(Corpus corpus) {
	for (p <- corpus, v := corpus[p]) {
		buildBinaries(p,v,overwrite=false);
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

public CFG cfgForExpression(map[NamePath,CFG] cfgs, Expr e) {
	return getOneFrom({ c | c <- cfgs<1>, /e := c});
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

public bool exprIsScalar(Expr e) {
	e = algebraicSimplification(e);
	return (scalar(s) := e && encapsed(_) !:= s);
}

public bool exprIsScalarString(Expr e) {
	e = algebraicSimplification(e);
	return (scalar(string(s)) := e);
}

public str getScalarString(Expr e) {
	e = algebraicSimplification(e);
	if (scalar(string(s)) := e) {
		return s;
	}
	throw "No value";
}

set[QueryResult] collapseVVInfo(VVInfo vv) {
	return toSet(vv.vvuses<2> + vv.vvcalls<2> + vv.vvmcalls<2> + vv.vvnews<2> + vv.vvprops<2> + vv.vvcconsts<2> + vv.vvscalls<2> +
		vv.vvstargets<2> + vv.vvsprops<2> + vv.vvsptargets<2>);
}

data ResolveStats = resolveStats(int resolved, int total, rel[loc,AnalysisName] resolvedLocs);

data PatternStats = patternStats(ResolveStats vvuses, ResolveStats vvcalls, ResolveStats vvmcalls, ResolveStats vvnews, ResolveStats vvprops,
								 ResolveStats vvcconsts, ResolveStats vvscalls, ResolveStats vvstargets, ResolveStats vvsprops, ResolveStats vvsptargets);

public rel[loc,AnalysisName] patternOne(str system, Maybe[System] ptopt = nothing()) {
	return patternOne(getBaseCorpus(), system, loadVVInfo(getBaseCorpus(), system), ptopt = ptopt);
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
public PatternStats patternOne(Corpus corpus, str system, VVInfo vv, Maybe[System] ptopt = nothing()) {
	// Load the ASTs for system
	pt = (just(aSystem) := ptopt) ? aSystem : loadBinary(system, corpus[system]);
	
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
		for (qr <- qrSet, e := qr.e, hasVariableForName(e)) {
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
				case e : {
					if (e@at == qr.l) {
						foreaches = [ fe | cn <- getTraversalContextNodes(), Stmt fe:foreach(_,_,_,var(name(name(v))),_) := cn ];
					} 
				}
			}
			
			if (!isEmpty(foreaches)) {
				fe = foreaches[0];
				if (fe.byRef) {
					println("Cannot use foreach, it creates an alias");
				} else {
					aexp = fe.arrayExpr;
					if (array(aelist) := aexp && false notin { exprIsScalarString(aeItem.val) | aeItem <- aelist }) {
						res = res + { < qr.l, varName(getScalarString(aeItem.val)) > | aeItem <- aelist };
					} else {
						println("Array expression <pp(aexp)> does not match pattern 1");
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

//data ResolveStats = resolveStats(int resolved, int total, rel[loc,AnalysisName] resolvedLocs);
//
//data PatternStats = patternStats(ResolveStats vvuses, ResolveStats vvcalls, ResolveStats vvmcalls, ResolveStats vvnews, ResolveStats vvprops,
//								 ResolveStats vvcconsts, ResolveStats vvscalls, ResolveStats vvstargets, ResolveStats vvsprops, ResolveStats vvsptargets);

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
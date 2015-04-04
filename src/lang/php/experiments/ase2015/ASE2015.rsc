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
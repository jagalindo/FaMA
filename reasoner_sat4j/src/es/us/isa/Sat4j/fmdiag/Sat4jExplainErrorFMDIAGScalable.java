package es.us.isa.Sat4j.fmdiag;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Exceptions.FAMAException;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.Reasoner.questions.ValidConfigurationErrorsQuestion;
import es.us.isa.FAMA.models.featureModel.GenericFeature;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.Sat4jReasoner.Sat4jQuestion;
import es.us.isa.Sat4jReasoner.Sat4jReasoner;
import es.us.isa.Sat4jReasoner.Sat4jResult;

public class Sat4jExplainErrorFMDIAGScalable extends Sat4jQuestion implements ValidConfigurationErrorsQuestion {

	public boolean returnAllPossibeExplanations = false;
	public Map<String, String> result = new HashMap<String, String>();

	Map<String, String> relations = null;
	public boolean flexactive = false;
	public int m = 1;
	private Sat4jReasoner reasoner;

	Product s, r;
	// public Map<String, Constraint> result = new HashMap<String, Constraint>();

	public void setConfiguration(Product s) {
		this.s = s;
	}

	public void setRequirement(Product r) {
		this.r = r;
	}

	public int numberOfPartitions = 4;
	public int baseSize = 100;

	public Sat4jExplainErrorFMDIAGScalable(int t) {
		this.numberOfPartitions = t;
	}

	public PerformanceResult answer(Reasoner r) throws FAMAException {
		reasoner = (Sat4jReasoner) r;
		// solve the problem y fmdiag
		relations = new HashMap<String, String>();

		Map<String, String> productConstraint = new HashMap<String, String>();
		ArrayList<String> feats = new ArrayList<String>();
		for (GenericFeature f : this.s.getFeatures()) {
			String cnfVar = reasoner.getCNFVar(f.getName());
			String name = "U_" + f.getName();
			productConstraint.put(name, "-" + cnfVar + " 0");
			feats.add(name);
		}

		Map<String, String> requirementConstraint = new HashMap<String, String>();
		for (GenericFeature f : this.r.getFeatures()) {
			String cnfVar = reasoner.getCNFVar(f.getName());
			requirementConstraint.put("R_" + f.getName(), cnfVar + " 0");
		}

		int cindex = 0;
		for (String cl : reasoner.clauses) {
			relations.put(cindex + "rel", cl);
		}
		relations.putAll(requirementConstraint);
		relations.putAll(productConstraint);

		// The use of this class is to force synced lists
		ArrayList<String> S = new ArrayList<String>(feats);
		ArrayList<String> AC = new ArrayList<String>(relations.keySet());

		if (returnAllPossibeExplanations == false) {

			List<String> fmdiag = fmdiag(S, AC);

			for (String s : fmdiag) {
				result.put(s, productConstraint.get(s));
			}

		} else {
			List<String> allExpl = new LinkedList<String>();
			List<String> fmdiag = fmdiag(S, AC);

			while (fmdiag.size() != 0) {
				allExpl.addAll(fmdiag);
				S.removeAll(fmdiag);
				AC.removeAll(fmdiag);
				fmdiag = fmdiag(S, AC);
			}
			for (String s : allExpl) {
				result.put(s, productConstraint.get(s));
			}
		}

		return new Sat4jResult();
	}

	public List<String> fmdiag(List<String> S, List<String> AC) { 
		// S is empty or (AC - S) non-consistent
		if (S.size() == 0 || !isConsistent(less(AC, S))) {
			return new ArrayList<String>();
		} else {
			// (AC + S) is non-consistent
			return diag(new ArrayList<String>(), S, AC);
		}
	}

	private List<String> less(List<String> aC, List<String> s2) {
		List<String> res = new ArrayList<String>();
		res.addAll(aC);
		res.removeAll(s2);
		return res;
	}

	public List<String> diag(List<String> D, List<String> S, List<String> AC) {
		/* 1st base case */
		if (D.size() != 0 && isConsistent(AC)) {
			/*
			 * Since AC does not contain D, when D is not empty and AC is consistent, then D
			 * contains inconsistencies then D is analyzed to look for them
			 */
			return new ArrayList<String>();
		}

		/*
		 * Since AC is non-consistent and D is not the inconsistencies source, then S is
		 * their source. If this algorithmic solution is 'flexible' and the size of S is
		 * lesser or equal than m, then S is the looked inconsistencies set (m defines
		 * the solution flexibility to contains some consistent rules).
		 *
		 * If this solution is not 'flexible' and S contains only one rule, then S is
		 * the looked inconsistent set
		 */

		/* 2nd base case */
		if (S.size() == 1) {
			return S;
		}

		/* outList corresponds to a results list */
		List<String> outList = new ArrayList<String>();

		//// *DIVISION PHASE*////
		int div = 0; // div is the size of the partitions

		if (S.size() >= numberOfPartitions) {
			div = S.size() / numberOfPartitions;
			if ((S.size() % numberOfPartitions) > 0) {
				div++;
			}
		} else
			div = 1;

		List<List<String>> splitListToSubLists = splitListToSubLists(S, div);

		//// *CONQUER PHASE*////
		List<List<String>> rest = new ArrayList<List<String>>();
		List<List<String>> less = new ArrayList<List<String>>();
		
		List<String> sPrevious = new ArrayList<String>();
		List<String> s = new ArrayList<String>();
				
		Integer res = 0; //res = 1 (partición s preferente es el origen de diagnóstico perso s no es mínima)
		         //res = 2 (partición s preferente es el origen de diagnóstico y es de tamaño mínimo)
		int j = 0; Integer posRes=-1;

		for (int i = splitListToSubLists.size() - 1; i >= 1; i--) {
			if (j > 0){
				sPrevious = plus(sPrevious, s);
			}	
			
		    s = splitListToSubLists.get(i); // S
			
			rest.add(getRest(s, splitListToSubLists)); // D
			less.add(less(AC, s));

			if (s.size()>0 && isConsistent(less.get(j))){
				if (s.size()==1){
					res = 2;
					outList = plus(outList, s);
				}else{
				    res = 1;
				}
				
				posRes=j;
				break;
			}
							
			j++;
		}

		if (res==0){ //Ninguna partición previa es causa de inconsistencia --> entonces la última partición es la causa!
			posRes = j;
			sPrevious = plus(sPrevious, s);
			
			//última partición
			s = splitListToSubLists.get(posRes);
			
			if (s.size()==1){ //Si fuera de tamaño 1
				res = 2;
				outList = plus(outList, s);
			}else{
			    res = 1;
			}
		}

		////2 opciones: partición mínima con diagnosis (res=2) o partición no-mínima con diagnosis (res=1)			
		if (res==2) {
		    s = sPrevious;
		    List<String> acc = less(AC, outList); //AC without results
		    outList = plus(outList, diag(outList, s, acc));
		}else{
			s = splitListToSubLists.get(splitListToSubLists.size() - 1 - posRes);
			List<String> resS = diag(new ArrayList<String>(), s, AC);
			
		
			if (sPrevious.size() > 0) //it is the 1st partition?
				outList = plus(outList, diag(resS, sPrevious, less(AC, resS)));
			else
				outList = plus(outList, resS);
		}
		
		return outList;
	}
	
	public <T> List<List<T>> splitListToSubLists(List<T> parentList, int subListSize){
		List<List<T>> subLists = new ArrayList<List<T>>();

		if (subListSize > parentList.size()) {
			subLists.add(parentList);
		} else {
			int remainingElements = parentList.size();
			int startIndex = 0;
			int endIndex = subListSize;
			do {
				List<T> subList = parentList.subList(startIndex, endIndex);
				subLists.add(new ArrayList<T>(subList));
				startIndex = endIndex;
				if (remainingElements - subListSize >= subListSize) {
					endIndex = startIndex + subListSize;
				} else {
					endIndex = startIndex + remainingElements - subList.size();
				}
				remainingElements -= subList.size();
			} while (remainingElements > 0);

		}
		return subLists;
	}

	private List<String> plus(List<String> a1, List<String> a2) {
		List<String> res = new ArrayList<String>();
		res.addAll(a1);
		res.addAll(a2);
		return res;
	}

	private List<String> getRest(List<String> s2, List<List<String>> splitListToSubLists) {
		List<String> res = new ArrayList<String>();

		for (List<String> c : splitListToSubLists) {
			if (c != s2) {
				res.addAll(c);
			}
		}
		return res;
	}

	private boolean isConsistent(Collection<String> aC) {
		// First we create the content of the cnf
		String cnf_content = "c CNF file\n";

		// We show as comments the variables's number
		Iterator<String> it = reasoner.variables.keySet().iterator();
		while (it.hasNext()) {
			String varName = it.next();
			cnf_content += "c var " + reasoner.variables.get(varName) + " = " + varName + "\n";
		}

		// Start the problem
		cnf_content += "p cnf " + reasoner.variables.size() + " " + (aC.size()) + "\n";
		// Clauses
		for (String cons : aC) {
			cnf_content += (String) relations.get(cons) + "\n";

		}

		// End file
		cnf_content += "0";
		ByteArrayInputStream stream = new ByteArrayInputStream(cnf_content.getBytes(StandardCharsets.UTF_8));

		ISolver s = SolverFactory.newDefault();
		Reader reader = new DimacsReader(s);
		try {
			reader.parseInstance(stream);
			return s.isSatisfiable();
		} catch (TimeoutException | ParseFormatException | ContradictionException | IOException e) {
			e.printStackTrace();

		}
		return false;

	}
	
	@Override
	public void setProduct(Product p) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isValid() {
		// TODO Auto-generated method stub
		return false;
	}

}
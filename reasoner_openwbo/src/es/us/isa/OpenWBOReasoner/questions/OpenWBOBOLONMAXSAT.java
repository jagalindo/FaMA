package es.us.isa.OpenWBOReasoner.questions;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import es.us.isa.FAMA.Benchmarking.PerformanceResult;
import es.us.isa.FAMA.Reasoner.Reasoner;
import es.us.isa.FAMA.models.variabilityModel.VariabilityElement;
import es.us.isa.FAMA.stagedConfigManager.Configuration;
import es.us.isa.OpenWBOReasoner.OpenWBOQuestion;
import es.us.isa.OpenWBOReasoner.OpenWBOReasoner;

public class OpenWBOBOLONMAXSAT extends OpenWBOQuestion{

	// This should be a full configuration
	public Configuration configuration;

	private ArrayList<String> configurationConstraints = new ArrayList<String>();
	private ArrayList<String> selectedConstraints = new ArrayList<String>();
	private ArrayList<String> deselectedConstraints = new ArrayList<String>();

	// Model Constraints
	private ArrayList<String> modelConstraints = new ArrayList<String>();

	// All Constraints
	private ArrayList<String> constraints = new ArrayList<String>();

	// All Variables
	private Map<String, String> variables;

	// Result
	public ArrayList<String> result = new ArrayList<String>();

	private OpenWBOReasoner reasoner;

	public void preAnswer(Reasoner r) {
		reasoner = (OpenWBOReasoner) r;

		// Generate all configuration constraints
		for (Entry<VariabilityElement, Integer> e : configuration.getElements().entrySet()) {
			String var = ((OpenWBOReasoner) r).getVariables().get(e.getKey().getName());
			String name = "C_" + e.getKey().getName();

			configurationConstraints.add(name);

			if (e.getValue() > 0) {
				selectedConstraints.add(var+" 0");
			} else if (e.getValue() == 0) {
				deselectedConstraints.add("-"+var+" 0");
			}
		}

		// Get all model constraints
		modelConstraints = ((OpenWBOReasoner) r).getClauses();

		// Add all Constraints
		constraints.addAll(modelConstraints);
		constraints.addAll(configurationConstraints);

		// Get all model variables
		variables = ((OpenWBOReasoner) r).variables;

	}
	
	
	public PerformanceResult answer(Reasoner r) {
		createSAT();
		return null;
	}

	
	private boolean createSAT() {
		//First calculate the top value.
		int top = deselectedConstraints.size()+1;
		
		
		// First we create the content of the cnf
		String cnf_content = "c CNF file\n";

		// We show as comments the variables's number
		Iterator<String> it = reasoner.variables.keySet().iterator();
		while (it.hasNext()) {
			String varName = it.next();
			cnf_content += "c var " + reasoner.variables.get(varName) + " = " + varName + "\n";
		}

		// Start the problem
		cnf_content += "p wcnf " + reasoner.variables.size() + " " + (-1 + modelConstraints.size()+selectedConstraints.size()+deselectedConstraints.size()) + " "+top+"\n";
		// Clauses
		it = modelConstraints.iterator();
		while (it.hasNext()) {
			cnf_content += top + " " + (String) it.next() + "\n";
		}

		for(String s: selectedConstraints) {
			cnf_content+= top + " " +s + "\n";
		}
		
		for(String s: deselectedConstraints) {
			cnf_content+= "1 " +s + "\n";
		}
		// End file
		cnf_content += "0";
		boolean res = false;
		try {
			//File tmpFile = File.createTempFile("cnf", "fm");
			File tmpFile = new File("C:\\glucose\\test.cnf");
			PrintWriter out = new PrintWriter(tmpFile);
			out.print(cnf_content);
			out.close();
//			Process p = Runtime.getRuntime().exec("bash.exe -c \"/mnt/c/glucose/glucose /mnt/c/glucose/test.cnf\"");
//			BufferedReader stdInput = new BufferedReader(new 
//				     InputStreamReader(p.getInputStream()));
//			String outStr ="";
//			String s = null;
//			while ((s = stdInput.readLine()) != null) {
//			    outStr+=s;
//			}
//			res=outStr.contains("UNSATISFIABLE");
//			
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return res;

	}
}

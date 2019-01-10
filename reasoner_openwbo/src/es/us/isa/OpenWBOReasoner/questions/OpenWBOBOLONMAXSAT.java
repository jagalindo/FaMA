package es.us.isa.OpenWBOReasoner.questions;

import java.util.ArrayList;
import java.util.Map;
import java.util.Map.Entry;

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
				selectedConstraints.add(name);
			} else if (e.getValue() == 0) {
				deselectedConstraints.add(name);
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
}

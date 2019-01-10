package main;

import es.us.isa.ChocoReasoner.ChocoReasoner;
import es.us.isa.ChocoReasoner.questions.ChocoBOLON;
import es.us.isa.ChocoReasoner.questions.ChocoBOLONFMDIAG;
import es.us.isa.FAMA.models.FAMAfeatureModel.FAMAFeatureModel;
import es.us.isa.FAMA.models.FAMAfeatureModel.fileformats.ProductWriterReader;
import es.us.isa.FAMA.models.FAMAfeatureModel.fileformats.XMLReader;
import es.us.isa.FAMA.models.featureModel.Product;
import es.us.isa.FAMA.models.variabilityModel.parsers.WrongFormatException;
import es.us.isa.GlucoseReasoner.GlucoseReasoner;
import es.us.isa.GlucoseReasoner.questions.GlucoseBOLONFMDIAGConfiguration;
import es.us.isa.OpenWBOReasoner.OpenWBOReasoner;
import es.us.isa.OpenWBOReasoner.questions.OpenWBOBOLONMAXSAT;

public class Experiment {

	public static void main(String[] args) throws WrongFormatException {

		String OP = args[0];
		String fmURI = args[1];
		String configurationURI = args[2];

		XMLReader reader = new XMLReader();
		ProductWriterReader prw= new ProductWriterReader();
		
		FAMAFeatureModel fm = (FAMAFeatureModel) reader.parseFile(fmURI);
		Product product = prw.readProduct(configurationURI);
		
		if (OP.equals("CSOP")) {

			ChocoReasoner reasoner = new ChocoReasoner();
			fm.transformTo(reasoner);
			
			ChocoBOLON op = new ChocoBOLON();
			op.configuration= product.toConfiguration(fm.getFeatures());
			reasoner.ask(op);
			//System.out.println("CSOP "+op.result);
				
		} else if (OP.equals("FMDIAG_CSOP")) {
			
			ChocoReasoner reasoner = new ChocoReasoner();
			fm.transformTo(reasoner);
			
			ChocoBOLONFMDIAG op = new ChocoBOLONFMDIAG();
			op.configuration= product.toConfiguration(fm.getFeatures());
			reasoner.ask(op);
			//System.out.println("FMDIAG_CSOP "+op.result);

		} else if (OP.equals("FMDIAG_SAT")) {

			GlucoseReasoner reasoner = new GlucoseReasoner();
			fm.transformTo(reasoner);
			
			GlucoseBOLONFMDIAGConfiguration op = new GlucoseBOLONFMDIAGConfiguration();
			op.configuration= product.toConfiguration(fm.getFeatures());
			reasoner.ask(op);
			System.out.println("FMDIAG_SAT "+op.result);
			
		} else if (OP.equals("MAXSAT")) {
			OpenWBOReasoner reasoner = new OpenWBOReasoner();
			fm.transformTo(reasoner);
			
			OpenWBOBOLONMAXSAT op = new OpenWBOBOLONMAXSAT();
			op.configuration= product.toConfiguration(fm.getFeatures());
			reasoner.ask(op);
			System.out.println("FMDIAG_SAT "+op.result);

		}

	}


}

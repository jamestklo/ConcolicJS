package ca.ubc.salt.concolicjs;

import java.io.File;
import java.io.IOException;

import org.apache.commons.io.FileUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.crawljax.core.CrawlerContext;
import com.crawljax.core.plugin.OnNewStatePlugin;
import com.crawljax.core.state.StateVertex;

public class DomAnalysisPlugin implements OnNewStatePlugin {
	private static final Logger LOG = LoggerFactory.getLogger(DomAnalysisPlugin.class);

	public void onNewState(CrawlerContext context, StateVertex newState) {
		try {
			Object s = context.getBrowser().executeJavaScript("return __domGraph(true);");
			LOG.info("state info file name:  " + s);
			File file = new File("analysis_of_state/" + newState.getId());
			FileUtils.write(file, (String) s);

		} 
		catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}

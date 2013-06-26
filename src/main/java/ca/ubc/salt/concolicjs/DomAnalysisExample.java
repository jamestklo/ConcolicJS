package ca.ubc.salt.concolicjs;

import java.io.File;
import java.io.IOException;
import java.util.concurrent.TimeUnit;

import org.apache.commons.io.FileUtils;

import com.crawljax.browser.EmbeddedBrowser.BrowserType;
import com.crawljax.core.CrawljaxRunner;
import com.crawljax.core.configuration.BrowserConfiguration;
import com.crawljax.core.configuration.CrawljaxConfiguration;
import com.crawljax.core.configuration.CrawljaxConfiguration.CrawljaxConfigurationBuilder;
import com.crawljax.core.configuration.ProxyConfiguration;
import com.crawljax.plugins.crawloverview.CrawlOverview;
import com.crawljax.plugins.proxy.WebScarabWrapper;

import edu.ubc.webscarab.MyProxyPlugin;

/**
 * Example of running Crawljax with the CrawlOverview plugin on a single-page web app. The crawl
 * will produce output using the {@link CrawlOverview} plugin.
 */
public final class DomAnalysisExample {

	private static final long WAIT_TIME_AFTER_EVENT = 30000;
	private static final long WAIT_TIME_AFTER_RELOAD = 30000;
	private static final String URL = "http://ca.yahoo.com";

	/**
	 * Run this method to start the crawl.
	 * 
	 * @throws IOException
	 *             when the output folder cannot be created or emptied.
	 */
	public static void main(String[] args) throws IOException {
		CrawljaxConfigurationBuilder builder = CrawljaxConfiguration.builderFor(URL);
		builder.crawlRules().insertRandomDataInInputForms(false);

		// click these elements

		builder.crawlRules().clickDefaultElements();
		builder.setMaximumStates(3);
		// Set timeouts
		builder.crawlRules().waitAfterReloadUrl(WAIT_TIME_AFTER_RELOAD, TimeUnit.MILLISECONDS);
		builder.crawlRules().waitAfterEvent(WAIT_TIME_AFTER_EVENT, TimeUnit.MILLISECONDS);

		WebScarabWrapper proxy = new WebScarabWrapper();
		proxy.addPlugin(new MyProxyPlugin());

		builder.setProxyConfig(ProxyConfiguration.manualProxyOn("localhost", 8084));

		File outFolder = new File("output");
		if (outFolder.exists()) {
			FileUtils.deleteDirectory(outFolder);
		}

		builder.addPlugin(new DomAnalysisPlugin());

		builder.addPlugin(proxy);
		builder.addPlugin(new CrawlOverview(outFolder));

		 System.setProperty("webdriver.chrome.driver", "lib/chromedriver");
		// We want to use two browsers simultaneously.
		builder.setBrowserConfig(new BrowserConfiguration(BrowserType.chrome, 1));

		CrawljaxRunner crawljax = new CrawljaxRunner(builder.build());
		crawljax.call();

	}
}

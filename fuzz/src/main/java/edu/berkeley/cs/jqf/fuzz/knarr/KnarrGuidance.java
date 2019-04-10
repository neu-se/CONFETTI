package edu.berkeley.cs.jqf.fuzz.knarr;

import edu.berkeley.cs.jqf.fuzz.central.KnarrClient;
import edu.berkeley.cs.jqf.fuzz.guidance.Guidance;
import edu.berkeley.cs.jqf.fuzz.guidance.GuidanceException;
import edu.berkeley.cs.jqf.fuzz.guidance.Result;
import edu.berkeley.cs.jqf.instrument.tracing.events.TraceEvent;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.function.Consumer;

public class KnarrGuidance implements Guidance {
    private byte[] input;
    private KnarrClient client;

    public KnarrGuidance() throws IOException  {
        this.client = new KnarrClient();
    }

    @Override
    public InputStream getInput() throws IllegalStateException, GuidanceException {
        return new ByteArrayInputStream(this.input);
    }

    @Override
    public boolean hasInput() {
        try {
            this.input = client.getInput();
        } catch (IOException e) {
            throw new Error(e);
        }

        return true;
    }

    @Override
    public void handleResult(Result result, Throwable error) throws GuidanceException {
        // Reset input
        this.input = null;
    }

    @Override
    public Consumer<TraceEvent> generateCallBack(Thread thread) {
        return new Consumer<TraceEvent>() {
            @Override
            public void accept(TraceEvent traceEvent) {
            }
        };
    }
}

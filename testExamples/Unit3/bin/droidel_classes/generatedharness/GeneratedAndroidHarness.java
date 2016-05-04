package generatedharness;

public final class GeneratedAndroidHarness {

  static final class AppStubs
      implements droidelhelpers.DroidelStubs {
    @Override
    public android.app.Application getApplication(String className) {
      return generatedstubs.GeneratedApplicationStubs.getApplication(className);
    }
    @Override
    public android.content.BroadcastReceiver getBroadcastReceiver(String className) {
      return generatedstubs.GeneratedBroadcastReceiverStubs.getBroadcastReceiver(className);
    }
    @Override
    public android.content.ContentProvider getContentProvider(String className) {
      return generatedstubs.GeneratedContentProviderStubs.getContentProvider(className);
    }
    @Override
    public android.app.Activity getActivity(String className) {
      return generatedstubs.GeneratedActivityStubs.getActivity(className);
    }
    @Override
    public android.app.Service getService(String className) {
      return generatedstubs.GeneratedServiceStubs.getService(className);
    }
    @Override
    public android.view.View inflateViewById(int id, android.content.Context ctx) {
      return generatedstubs.GeneratedAndroidLayoutStubs.inflateViewById(id, ctx);
    }
    @Override
    public android.support.v4.app.Fragment getSupportFragment(String className) {
      return generatedstubs.GeneratedAndroidLayoutStubs.getSupportFragment(className);
    }
    @Override
    public android.app.Fragment getAppFragment(String className) {
      return generatedstubs.GeneratedAndroidLayoutStubs.getAppFragment(className);
    }
    @Override
    public void callXMLRegisteredCallback(android.content.Context context, android.view.View view) {
      generatedstubs.GeneratedAndroidXMLCallbackStubs.callXMLRegisteredCallback(context, view);
    }
  }

  public static void androidMain() {
    android.app.ActivityThread.main(new AppStubs());
  }
}

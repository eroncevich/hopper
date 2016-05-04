package generatedstubs;

import android.view.WindowManager;
import android.os.Vibrator;
import android.location.LocationManager;
import android.view.accessibility.AccessibilityManager;
import android.app.NotificationManager;
import android.app.UiModeManager;
import android.media.AudioManager;
import android.accounts.AccountManager;
import android.net.ConnectivityManager;
import android.net.wifi.WifiManager;
import android.os.PowerManager;
import android.app.ActivityManager;
import android.app.KeyguardManager;
import android.app.DownloadManager;
import android.view.inputmethod.InputMethodManager;
import android.app.AlarmManager;
import android.app.SearchManager;
import android.view.LayoutInflater;

public final class GeneratedAndroidSystemServiceStubs {
  private static WindowManager window;
  private static Vibrator vibrator;
  private static LocationManager location;
  private static AccessibilityManager accessibility;
  private static NotificationManager notification;
  private static UiModeManager uimode;
  private static AudioManager audio;
  private static AccountManager account;
  private static ConnectivityManager connection;
  private static WifiManager wifi;
  private static PowerManager power;
  private static ActivityManager activity;
  private static KeyguardManager keyguard;
  private static DownloadManager download;
  private static InputMethodManager input_method;
  private static AlarmManager alarm;
  private static SearchManager search;
  private static LayoutInflater layout_inflater;

  static {
    try {
      android.view.DisplayAdjustments loc_1 = android.view.DisplayAdjustments.DEFAULT_DISPLAY_ADJUSTMENTS;
      android.view.DisplayInfo loc_2 = new android.view.DisplayInfo();
      android.hardware.display.DisplayManagerGlobal loc_3 = android.hardware.display.DisplayManagerGlobal.getInstance();
      android.view.Display loc_4 = new android.view.Display(loc_3, 0, loc_2, loc_1);
      android.view.WindowManagerImpl loc_5 = new android.view.WindowManagerImpl(loc_4);
      android.os.NullVibrator loc_6 = android.os.NullVibrator.getInstance();
      android.content.Context loc_7 = null;
      android.content.ContextWrapper loc_8 = new android.content.ContextWrapper(loc_7);
      android.content.Context loc_9 = loc_8;
      com.android.server.LocationManagerService loc_10 = new com.android.server.LocationManagerService(loc_9);
      android.location.ILocationManager loc_11 = loc_10;
      com.android.server.accessibility.AccessibilityManagerService loc_12 = new com.android.server.accessibility.AccessibilityManagerService(loc_9);
      android.view.accessibility.IAccessibilityManager loc_13 = loc_12;
      com.android.server.accounts.AccountManagerService loc_14 = new com.android.server.accounts.AccountManagerService(loc_9);
      android.accounts.IAccountManager loc_15 = loc_14;
      com.android.server.NetworkManagementService loc_16 = com.android.server.NetworkManagementService.create(loc_9);
      android.os.INetworkManagementService loc_17 = loc_16;
      android.app.IAlarmManager loc_18 = (android.app.IAlarmManager) null;
      com.android.server.net.NetworkStatsService loc_19 = new com.android.server.net.NetworkStatsService(loc_9, loc_17, loc_18);
      android.net.INetworkStatsService loc_20 = loc_19;
      com.android.server.power.PowerManagerService loc_21 = new com.android.server.power.PowerManagerService();
      android.os.IPowerManager loc_22 = loc_21;
      com.android.server.am.ActivityManagerService loc_23 = com.android.server.am.ActivityManagerService.self();
      android.app.IActivityManager loc_24 = loc_23;
      com.android.server.net.NetworkPolicyManagerService loc_25 = new com.android.server.net.NetworkPolicyManagerService(loc_9, loc_24, loc_22, loc_20, loc_17);
      android.net.INetworkPolicyManager loc_26 = loc_25;
      com.android.server.ConnectivityService loc_27 = new com.android.server.ConnectivityService(loc_9, loc_17, loc_20, loc_26);
      android.net.IConnectivityManager loc_28 = loc_27;
      com.android.server.wifi.WifiService loc_29 = new com.android.server.wifi.WifiService(loc_9);
      android.net.wifi.IWifiManager loc_30 = loc_29;
      android.os.Handler loc_31 = new android.os.Handler();
      java.lang.String loc_32 = new java.lang.String();
      android.test.mock.MockContentResolver loc_33 = new android.test.mock.MockContentResolver();
      android.content.ContentResolver loc_34 = loc_33;
      com.android.internal.policy.impl.PhoneLayoutInflater loc_35 = new com.android.internal.policy.impl.PhoneLayoutInflater(loc_9);
      window = loc_5;
      vibrator = loc_6;
      location = new android.location.LocationManager(loc_9, loc_11);
      accessibility = new android.view.accessibility.AccessibilityManager(loc_9, loc_13, 0);
      notification = android.app.NotificationManager.from(loc_9);
      uimode = (android.app.UiModeManager) null;
      audio = new android.media.AudioManager(loc_9);
      account = new android.accounts.AccountManager(loc_9, loc_15);
      connection = new android.net.ConnectivityManager(loc_28);
      wifi = new android.net.wifi.WifiManager(loc_9, loc_30);
      power = new android.os.PowerManager(loc_9, loc_22, loc_31);
      activity = (android.app.ActivityManager) null;
      keyguard = (android.app.KeyguardManager) null;
      download = new android.app.DownloadManager(loc_34, loc_32);
      input_method = android.view.inputmethod.InputMethodManager.getInstance();
      alarm = (android.app.AlarmManager) null;
      search = (android.app.SearchManager) null;
      layout_inflater = loc_35;
    }
    catch (Exception e) {
    }
  }

  public static Object getSystemService(String name) {
    if(name.equals("window")) return window;
    if(name.equals("vibrator")) return vibrator;
    if(name.equals("location")) return location;
    if(name.equals("accessibility")) return accessibility;
    if(name.equals("notification")) return notification;
    if(name.equals("uimode")) return uimode;
    if(name.equals("audio")) return audio;
    if(name.equals("account")) return account;
    if(name.equals("connection")) return connection;
    if(name.equals("wifi")) return wifi;
    if(name.equals("power")) return power;
    if(name.equals("activity")) return activity;
    if(name.equals("keyguard")) return keyguard;
    if(name.equals("download")) return download;
    if(name.equals("input_method")) return input_method;
    if(name.equals("alarm")) return alarm;
    if(name.equals("search")) return search;
    if(name.equals("layout_inflater")) return layout_inflater;
    return null;
  }
}

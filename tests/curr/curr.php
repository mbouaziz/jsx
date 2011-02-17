<?
header('Access-Control-Allow-Origin: *');
//  header('Access-Control: allow <*>');
  $rates = array('EUR' => array(
  	   	       'EUR' => 1,
		       'RUB' => 39.6324,
		       'USD' => 1.35626,
		       ),
		 'RUB' => array(
		       'EUR' => 0.02523,
		       'RUB' => 1,
		       'USD' => 0.03422,
		       ),
		 'USD' => array(
		       'EUR' => 0.73732,
		       'RUB' => 29.2219,
		       'USD' => 1,
		       ),
		);

  $i = $_REQUEST['i'];
  $o = $_REQUEST['o'];
  $rate = (isset($rates[$i]) && isset($rates[$i][$o])) ? $rates[$i][$o] : 0;
  $a = isset($_REQUEST['a']) ? $_REQUEST['a'] : 1;
  echo $a * $rate;
?>
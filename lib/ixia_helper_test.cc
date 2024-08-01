#include "lib/ixia_helper.h"

#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "gutil/proto_matchers.h"
#include "gutil/status_matchers.h"

namespace pins_test::ixia {

using ::gutil::EqualsProto;
using ::gutil::IsOkAndHolds;

TEST(ParseTrafficItemStats, ParsesExampleCorrectly) {
  static constexpr absl::string_view kExample = R"json({
      "rowCount": 2,
      "rowValues": {
        "arg1": [
          [
            "Ethernet - 001",
            "Ethernet - 003",
            "Unicast Traffic",
            "Unicast Traffic-Main Traffic - Flow Group 0001",
            "115052349",
            "115052349",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "174189256386",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "1088",
            "1081",
            "6314",
            "00:00:00.175",
            "00:00:08.885"
          ]
        ],
        "arg2": [
          [
            "Ethernet - 002",
            "Ethernet - 003",
            "Unicast Traffic #1",
            "Unicast Traffic #1-Secondary traffic - Flow Group 0001",
            "105",
            "105",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "158970",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "3711",
            "1093",
            "6306",
            "00:00:00.175",
            "00:00:00.175"
          ]
        ]
      },
      "egressMode": "conditional",
      "currentPage": 1,
      "timestamp": 360000,
      "isReady": true,
      "allowPaging": true,
      "totalPages": 1,
      "totalRows": 2,
      "pageSize": 50,
      "columnCaptions": [
        "Tx Port",
        "Rx Port",
        "Traffic Item",
        "Flow Group",
        "Tx Frames",
        "Rx Frames",
        "Frames Delta",
        "Loss %",
        "Tx Frame Rate",
        "Rx Frame Rate",
        "Tx L1 Rate (bps)",
        "Rx L1 Rate (bps)",
        "Rx Bytes",
        "Tx Rate (Bps)",
        "Rx Rate (Bps)",
        "Tx Rate (bps)",
        "Rx Rate (bps)",
        "Tx Rate (Kbps)",
        "Rx Rate (Kbps)",
        "Tx Rate (Mbps)",
        "Rx Rate (Mbps)",
        "Store-Forward Avg Latency (ns)",
        "Store-Forward Min Latency (ns)",
        "Store-Forward Max Latency (ns)",
        "First TimeStamp",
        "Last TimeStamp"
      ],
      "pageValues": [
        [
          [
            "Ethernet - 001",
            "Ethernet - 003",
            "Unicast Traffic",
            "Unicast Traffic-Main Traffic - Flow Group 0001",
            "115052349",
            "115052349",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "174189256386",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "1088",
            "1081",
            "6314",
            "00:00:00.175",
            "00:00:08.885"
          ]
        ],
        [
          [
            "Ethernet - 002",
            "Ethernet - 003",
            "Unicast Traffic #1",
            "Unicast Traffic #1-Secondary traffic - Flow Group 0001",
            "105",
            "105",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "158970",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "0",
            "3711",
            "1093",
            "6306",
            "00:00:00.175",
            "00:00:00.175"
          ]
        ]
      ],
      "columnCount": 26,
      "isBlocked": false,
      "egressPageSize": "This operation is not supported as this is not an ingress/egress view",
      "links": [
        {
          "rel": "self",
          "method": "GET",
          "href": "/api/v1/sessions/1239/ixnetwork/statistics/view/9/data"
        },
        {
          "rel": "meta",
          "method": "OPTIONS",
          "href": "/api/v1/sessions/1239/ixnetwork/statistics/view/9/data"
        }
      ]
    })json";

  EXPECT_THAT(ParseTrafficItemStats(kExample), IsOkAndHolds(EqualsProto(R"pb(
                stats_by_traffic_item {
                  key: "Unicast Traffic"
                  value: {
                    tx_port: "Ethernet - 001"
                    rx_port: "Ethernet - 003"
                    traffic_item_name: "Unicast Traffic"
                    num_tx_frames: 115052349
                    num_rx_frames: 115052349
                    rx_bytes: 174189256386
                    first_time_stamp: 0.175
                    last_time_stamp: 8.885

                  }
                }

                stats_by_traffic_item {
                  key: "Unicast Traffic #1"
                  value: {
                    tx_port: "Ethernet - 002"
                    rx_port: "Ethernet - 003"
                    traffic_item_name: "Unicast Traffic #1"
                    num_tx_frames: 105
                    num_rx_frames: 105
                    rx_bytes: 158970
                    first_time_stamp: 0.175
                    last_time_stamp: 0.175
                  }
                }
              )pb")));
}

}  // namespace pins_test::ixia

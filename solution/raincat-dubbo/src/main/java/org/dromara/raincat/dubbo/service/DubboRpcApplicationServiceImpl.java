/*
 *
 *
 * This copyrighted material is made available to anyone wishing to use, modify,
 * copy, or redistribute it subject to the terms and conditions of the GNU
 * Lesser General Public License, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public License
 * for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this distribution; if not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.dromara.raincat.dubbo.service;

import com.alibaba.dubbo.config.ApplicationConfig;
import org.dromara.raincat.core.service.RpcApplicationService;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;

import java.util.Optional;

/**
 * DubboRpcApplicationServiceImpl.
 * @author xiaoyu
 */
@Service("rpcApplicationService")
public class DubboRpcApplicationServiceImpl implements RpcApplicationService {

    /**
     * dubbo ApplicationConfig.
     */
    @Autowired(required = false)
    private ApplicationConfig applicationConfig;

    @Override
    public String findModelName() {
        return Optional.ofNullable(applicationConfig).orElse(new ApplicationConfig("tx-transaction-dubbo")).getName();

    }
}
